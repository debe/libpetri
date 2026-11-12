# 11 — Modular Composition

This document specifies the **modular composition** extension of the CTPN engine: open net fragments (subnets) with declared interfaces, instantiation, structural composition by port mapping, synchronous channel fusion of interface transitions, action binding per instance, and orthogonal fusion of N places.

The vocabulary follows the ISO/IEC 15909-2 PNML *modular extension*: an open net is a Petri net augmented with an **interface** consisting of **interface places** (ports) and **interface transitions** (synchronous channels). A **module instance** is a renamed copy of an open net wired into an enclosing net by mapping its interface elements to enclosing-net elements.

Composition is **build-time only**. The runtime, exporter, verifier, and event subsystems see a normal flat `PetriNet` after composition completes. No semantic primitive in this document changes the contract of CORE, EXEC, CONC, EVT, ENV, VER, EXP, or PERF for the resulting flat net.

---

## Subnet Definition

#### MOD-001: SubnetDef Definition (open net + interface)

**Priority:** MUST
**Kind:** F

A **subnet definition** is an open Petri net fragment paired with a declared **interface**. The fragment is a structurally complete net definition (places, transitions, arcs, timing, priority, optional actions) per [CORE-040]; the interface enumerates which of its places are exposed as **ports** and which of its transitions are exposed as **synchronous channels**.

A subnet definition MAY be parameterised by a typed `Params` value supplied at instantiation time (see [MOD-010]). When unparameterised, the parameter type is the implementation's unit/void type.

Building a subnet definition fails in the cases of [MOD-006]; this requirement says what a successful build returns. The body is the net that the net builder builds from the declared places, transitions and terminal places ([CORE-040]), so its places include every place an arc of a body transition names. The order in which the interface lists its ports and channels is not specified. As in [TIME-010], the transitions of one body are assumed to have pairwise distinct names.

*When* building the subnet definition succeeds, its interface *shall* hold exactly the declared ports, each with the name, direction and place it was declared with.

*When* building the subnet definition succeeds, its interface *shall* hold exactly the declared channels, each with the name and transition it was declared with.

*When* building the subnet definition succeeds, its body *shall* hold the places and terminal places of the net that the net builder builds from the declaration, and the declared transitions in the order they were added, none of them renamed.

*When* building the subnet definition succeeds, the subnet definition *shall* keep the name it was declared with.

*When* the net builder builds the body and the interface declares no port and no channel, building the subnet definition *shall* succeed.

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
**Kind:** Q

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
**Kind:** B

An **interface place** (port) declares:
1. A **name** unique within the interface.
2. A **direction**: `Input`, `Output`, or `InOut`.
3. The underlying `Place<T>` from the body net it exposes.

The exposed place MUST be a place of the subnet's body. Two distinct ports MAY expose the same body place, whatever their directions. When two ports expose one body place, a caller binds both to one caller place; which binding a composition keeps when they are bound to two different caller places is not defined ([MOD-020]).

*If* two ports of one interface have the same name, *then* building the subnet definition *shall* fail.

*If* the net builder builds the body and a port exposes a place that is not a place of the built body, *then* building the subnet definition *shall* fail.

*When* building a subnet definition succeeds, building it with one more port, whose name no port of the interface has and which exposes the place of one of its ports, *shall* also succeed, whatever the directions of the two ports.

**Acceptance Criteria:**
1. A port can be declared with name, direction, and a body place.
2. The port name is unique within an interface (duplicate names rejected at build).
3. The exposed place's token type is preserved in the port's typed handle (see [MOD-011]).
4. A port whose underlying place is not present in the body net is rejected at build (see [MOD-006]).
5. Two ports with different names over one body place build, whatever their directions.

**Test derivation:** Build an interface with ports `in: Input<String>` and `out: Output<String>`; verify both names and directions retrievable. Attempt to declare two ports with the same name; verify rejection. Attempt to declare a port over a place not in the body; verify rejection. Declare a second port with another name over the place of `in`, once as `Input` and once as `Output`; verify that both subnets build.

---

#### MOD-004: Port Direction Semantics (advisory; arcs govern flow)

**Priority:** MUST
**Kind:** B

Port direction is **advisory metadata**: the subnet builder, `instantiate` and composition do not read it. Documentation, visualization and the verification harness of [MOD-051] read it. It does NOT constrain arc flow at runtime: an `Output` port's place MAY have input arcs from internal transitions; an `Input` port's place MAY be read by internal transitions. Actual token flow at run time is governed exclusively by arcs declared per CORE-030..CORE-035.

Implementations MAY emit a build-time warning when declared direction conflicts with the arc structure (e.g., an `Input` port whose place has no internal consumer transition), but MUST NOT reject the subnet on direction-versus-arc mismatch.

*When* two subnet declarations differ only in the directions of their ports, building the subnet definition *shall* succeed for both or fail for both.

*When* two subnet definitions differ only in the directions of their ports, `instantiate` with one prefix *shall* succeed for both or fail for both, and two successes *shall* give the same places, the same transitions, the same port and channel handles, and the same ports apart from their directions.

*When* building a subnet definition succeeds, the definition *shall* have a port with the name of each declared port, and each such port *shall* carry the declared direction.

**Acceptance Criteria:**
1. Direction metadata is preserved and queryable via the port handle.
2. A subnet whose `Output` port place is also written internally by transitions is accepted at build.
3. A subnet whose `Input` port place is also read internally by transitions is accepted at build.
4. Where a warning channel exists, an obvious mismatch (declared `Input` with no internal consumer; declared `Output` with no internal producer) MAY emit a warning but MUST NOT raise an error.

**Test derivation:** Build a subnet whose `Output` port place has both an internal output arc (producer) and an internal input arc (consumer); verify build succeeds.

---

#### MOD-005: Channel Declaration (interface transitions for synchronous fusion)

**Priority:** MUST
**Kind:** B

An **interface transition** (synchronous channel) declares:
1. A **name** unique within the interface (sharing namespace with port names is implementation-defined; collisions MUST be rejected if they share a namespace).
2. The underlying `Transition` from the body net it exposes.

A channel MAY be bound at composition time to a caller-side transition, producing a single merged transition in the composed net (see [MOD-021]). Channels are the synchronization primitive for cross-instance and host-instance coupling at the transition level; ports synchronize at the place level.

As in [MOD-006], a channel whose transition has the name of no body transition is rejected, a channel over a transition of the body is accepted, and a channel over a second transition object that has the name of a body transition is implementation-defined. For subnet definitions [MOD-006] settles the namespace choice of item 1: port names and channel names are two namespaces.

*If* two channels of the interface have the same name, *then* building the subnet definition *shall* fail.

*If* a channel of the interface exposes a transition whose name is not the name of a transition of the built body, *then* building the subnet definition *shall* fail.

*When* the net builder builds the body, the subnet definition builds without its channels, every channel exposes a transition of the built body, no two channels have the same name, and no channel has the name of a port, building the subnet definition with its channels *shall* succeed.

**Acceptance Criteria:**
1. A channel can be declared with a name and a body transition.
2. The channel name is unique within its namespace.
3. The exposed transition's identity is preserved through the channel handle (see [MOD-011]).
4. A channel whose underlying transition is not present in the body net is rejected at build (see [MOD-006]).

**Test derivation:** Build an interface with one channel exposing a transition `attempt`; verify the channel handle resolves to the same transition identity in the renamed body. Attempt to declare two channels with the same name; verify rejection.

---

#### MOD-006: Subnet Validation at Build

**Priority:** MUST
**Kind:** B

Construction of a subnet definition MUST validate the interface against the body before producing an immutable result. The body is the net that the net builder builds, and the places and transitions of the body are those of that net ([CORE-040]). Validation MUST reject:
1. A port whose underlying place is not present in the body.
2. A channel whose underlying transition is not present in the body.
3. Duplicate port names within the interface.
4. Duplicate channel names within the interface.
5. A body that the net builder rejects ([CORE-040], [EXEC-042]).

Each failure MUST produce an error identifying the offending element by name.

Duplicate names (cases 3 and 4) do not depend on the body and may be checked before the body is built. Port names and channel names are two namespaces: a port and a channel may have the same name. This settles for subnet definitions the choice that [MOD-005] leaves to the implementation.

A channel whose transition has the name of no body transition is rejected in every implementation (case 2), and a channel over a transition of the body is accepted in every implementation. Whether a channel over a second transition object that has the name of a body transition is accepted is implementation-defined: Java and TypeScript compare transition objects and reject it, Rust and Python compare names and accept it. As in [TIME-010], the transitions of one body are assumed to have pairwise distinct names; no builder checks this.

A terminal place that the body declares ([EXEC-042]) and that no body transition consumes from or reads is not by itself a reason to reject at subnet build; `instantiate` and composition refuse such a body ([EXEC-042], [MOD-010]).

*If* a port of the interface exposes a place that is not a place of the built body, *then* building the subnet definition *shall* fail.

*If* a channel of the interface exposes a transition whose name is not the name of a transition of the built body, *then* building the subnet definition *shall* fail.

*If* two ports of the interface have the same name, *then* building the subnet definition *shall* fail.

*If* two channels of the interface have the same name, *then* building the subnet definition *shall* fail.

*If* the net builder rejects the body, *then* building the subnet definition *shall* fail.

*When* the net builder builds the body, every port exposes a place of the built body, every channel exposes a transition of the built body, and no two ports and no two channels have the same name, building the subnet definition *shall* succeed.

*When* building the subnet definition fails, the error message *shall* contain the message with which the net builder rejected the body, or the name of a port or channel that meets one of the rejection cases 1 to 4.

**Acceptance Criteria:**
1. Each rejection case above produces an error at subnet build, not later at instantiation or composition.
2. Error messages name the offending port, channel, place, or transition.
3. A valid subnet definition is immutable after build.

**Test derivation:** Construct invalid subnets covering rejection cases 1 to 4; verify each fails at build with a message naming the offending element. Case 5 has no test: the subnet-definition builder takes only places, transitions, ports and channels, the net builder rejects none of these on its own, and `fromNet` ([MOD-014]) takes a net that is already built.

---

## Instantiation

#### MOD-010: Instance Creation via instantiate(prefix, params)

**Priority:** MUST
**Kind:** F

A subnet definition produces a **module instance** via `instantiate(prefix, params)`. Instantiation:
1. Takes a string `prefix` and a `params` value matching the subnet's parameter type.
2. Produces a renamed copy of the body net where every place name and every transition name is rewritten as `prefix + "/" + originalName`.
3. The renamed body is a structurally valid `PetriNet` per [CORE-040].
4. Arcs in the renamed body reference the renamed places; the arc topology is identical to the body's arc topology modulo the rename.
5. Timing, priority, and action of each transition are preserved (actions are shared by reference; see [MOD-030]).

The separator `"/"` is reserved by this requirement as the prefix separator. Implementations MUST use exactly `"/"`. Nested instantiation produces names of the form `outer/inner/originalName` (see [MOD-013]).

*If* the prefix given to `instantiate` is empty or contains `/`, *then* `instantiate` *shall* fail.

*When* `instantiate` is given a non-empty prefix that contains no `/` and the body of the subnet definition declares no terminal place ([EXEC-042]), `instantiate` *shall* succeed.

*If* the prefix given to `instantiate` is non-empty and contains no `/` and the body of the subnet definition declares a terminal place ([EXEC-042]), *then* `instantiate` *shall* fail with an error that names one of those terminal places.

*When* `instantiate` succeeds with prefix `p`, the renamed body *shall* hold exactly the body's places and, in the body's order, the body's transitions, each renamed from `x` to `p/x`, with every arc and output specification of a transition naming the renamed places and its timing, priority and action unchanged.

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
**Kind:** F

A module instance MUST expose typed lookup handles:
1. `port(name, type)` returns the renamed `Place<T>` corresponding to the named port from the original interface.
2. `channel(name)` returns the renamed `Transition` corresponding to the named channel from the original interface.
3. `params()` returns the parameter value supplied at instantiation.
4. `prefix()` returns the prefix string supplied at instantiation.

Java and TypeScript return the renamed `Transition` from `channel(name)`; Rust and Python return its name, which identifies it, since transitions are identified by name. Python's port lookup is `port_place_name(name)`, which returns the renamed place's name, and Python's definitions take no parameters, so its instances have no `params()`.

In an implementation that keeps a run-time token type for each port (Java, Rust), the type `T` requested from `port` MUST match the port's originally declared token type, and a mismatch MUST be reported as an error. TypeScript's `port<T>(name)` takes `T` as an annotation it does not check, and Python's lookup takes no type.

*When* `instantiate` succeeds with prefix `p` and the interface declares a port named `n` that exposes the body place `x`, the instance's port lookup for `n` *shall* return the place `x` renamed under `p`, the place `p/x`.

*When* `instantiate` succeeds with prefix `p` and the interface declares a channel named `n` that exposes the body transition `t`, the instance's channel lookup for `n` *shall* return the renamed transition `p/t`.

*If* the port lookup of an instance is given a name that is not a port of the interface, *then* the lookup *shall* fail.

*If* the channel lookup of an instance is given a name that is not a channel of the interface, *then* the lookup *shall* fail.

*When* `instantiate` succeeds with prefix `p`, the instance's `prefix()` *shall* return `p`.

*Where* an implementation keeps a run-time token type for each port (Java, Rust), *when* a port lookup names a port of the interface and requests the token type of the place that the port lookup returns, the lookup *shall* return that place.

*Where* an implementation keeps a run-time token type for each port (Java, Rust), *if* a port lookup names a port of the interface and requests a token type other than the type of the place that the port lookup returns, *then* the lookup *shall* fail.

*Where* an implementation keeps a run-time token type for each port (Java, Rust), *if* a port lookup names no port of the interface, *then* the lookup *shall* fail, whatever type it requests.

**Acceptance Criteria:**
1. `port("input", String)` on an instance whose interface declared `input: Input<String>` returns the renamed `Place<String>`.
2. In an implementation that keeps a run-time token type for each port (Java, Rust), `port("input", Integer)` on the same instance is rejected with an error.
3. `channel("attempt")` returns the renamed `Transition` whose original name was `attempt`.
4. Looking up a port or channel name that does not exist in the interface produces an error.
5. In an implementation whose instances carry parameters (Java, TypeScript, Rust), `params()` returns the value passed to `instantiate`.

**Depends on:** [MOD-003], [MOD-005], [MOD-010]
**Test derivation:** Build a subnet with port `input: Input<String>` and channel `attempt`; instantiate with prefix `r1`; verify `port("input", String)` returns the renamed place and `channel("attempt")` returns the renamed transition.

---

#### MOD-012: Per-Instance State Isolation

**Priority:** MUST
**Kind:** B

The private runtime state of each module instance is independent of every other instance. A place of an instance is **private** to it when no port binding names it, as the caller place or as the port place the binding replaces ([MOD-020]), no fusion set lists it ([MOD-060]), no transition of the instance that a channel binding merges names it ([MOD-021]), and no transition outside the instance names it: no hand-added transition, no caller-side definition of a channel binding, no transition of another instance and no directly composed subnet ([MOD-025]). An auto-composition ([MOD-024]) of an instance under prefix `q` counts as binding a place `x` when `x` is the unrenamed place of one of that instance's ports or when `q/x` is a place of that instance, whether or not the call binds it. Port bindings, channels and fusion sets are how instances share state on purpose, so isolation covers private places only.

After composition into a flat net, private places of two distinct instances MUST occupy distinct slots in the compiled net's place index, hold disjoint token bags, and evolve independently under the executor.

This isolation is a structural consequence of name-prefixing per [MOD-010] (distinct prefixed names → distinct place identities → distinct slots). No additional runtime mechanism is required.

Private place token state, the enablement state of a transition whose arc places are all private, and the timing clock of such a transition (per [TIME-010], [TIME-011]) MUST all be per-instance.

In the sentences below, `a` and `b` are single-segment prefixes: non-empty and without `/` ([MOD-010]). For two instances nested in one outer instance ([MOD-013]), the sentences apply to the build of the outer subnet's body, where their prefixes are single segments.

*When* a net is built by composition, each of its transitions that names a place private to the instance under prefix `b` *shall* have a name of the form `b/x`.

*When* a transition whose name has the form `a/x` fires in a net built by composition, every place private to the instance under another prefix `b` *shall* keep its token count.

*When* a `compose(instance, bindings)` call ([MOD-020]) adds a transition of the instance under prefix `b` that names a place private to that instance, the built net *shall* hold a transition of the same name that names that place.

*When* a transition whose name has the form `a/x` fires in a net built by composition, each transition named `b/y`, for another prefix `b`, whose arc places are all private to the instance under `b` *shall* keep its enablement and its armed state, and its stamp if it is armed.

*When* a transition whose name has the form `a/x` is reaped, or the firing clock advances in a net that holds such a transition, each transition named `b/y`, for another prefix `b`, *shall* keep its armed state and its stamp.

**Acceptance Criteria:**
1. Compose two instances of the same subnet definition (different prefixes) into one net; build and execute. Tokens added to instance A's private place do not appear in instance B's corresponding private place.
2. Firing a transition in instance A does not affect the enablement of a transition in instance B whose arc places are all private to B.
3. Firing a transition in instance A does not change the timing clock of a transition in instance B whose arc places are all private to B; reaping a transition of A, or advancing the clock, changes no timing clock in B.
4. Compose three instances A, B and C of one subnet definition and fuse a caller place with a place of C; after build, each transition of A and of B still names its own private places.

**Depends on:** [MOD-010], [MOD-020], [MOD-021], [MOD-024], [MOD-025], [MOD-060], [CORE-070], [TIME-010], [TIME-011], [TIME-012], [TIME-013]
**Test derivation:** Build a bounded-buffer subnet; compose two instances `b1` and `b2`; add tokens to `b1/slots`; verify `b2/slots` token count unchanged.

---

#### MOD-013: Nested Instantiation (prefix concatenation associative)

**Priority:** MUST
**Kind:** F

A subnet that itself composes other subnets can be instantiated like any other subnet: the third sentence below makes `instantiate` accept it. The runtimes build such a subnet definition with `fromNet` ([MOD-014]) over a net that composes an instance ([MOD-020]). The resulting nested names use `"/"` as the separator at every level: `outer/inner/originalName`.

Prefix concatenation is associative on names: instantiating a subnet `S` (which internally composes an instance `inner` of subnet `T`) with prefix `outer` gives the name `outer/inner/x` for every place `x` of `T` that the body of `S` holds as `inner/x`, and `outer/inner/x` is `x` renamed under the concatenated prefix `outer/inner`. So the nested names are the names of `T` that the body of `S` holds, renamed under `outer/inner`. No single `instantiate` call produces them, because `outer/inner` contains `/` and is not a valid prefix ([MOD-010]).

Which places and transitions of `T` the body of `S` holds is decided by the composition. A port place of `T` that `S` binds to a place of its own is replaced by that place and does not become `outer/inner/x` ([MOD-020]). An internal place of `T` that no arc names is not added by the composition ([MOD-020]). A transition of `T` merged with a caller transition through a channel takes the caller's name ([MOD-021]).

*When* the body of a subnet definition `S` holds the place `i/x` of an instance under prefix `i` of a subnet definition `T`, for a place `x` of `T`, and `S` is instantiated with prefix `o`, the instance *shall* hold the place `o/i/x`.

*When* the body of a subnet definition `S` holds the transition `i/t` of an instance under prefix `i` of a subnet definition `T`, for a transition `t` of `T`, and `S` is instantiated with prefix `o`, the instance *shall* hold the transition `o/i/t`.

*When* `instantiate` is given a non-empty prefix that contains no `/` and the body of the subnet definition declares no terminal place, `instantiate` *shall* succeed, also when names of the body contain `/` because the body holds a composed instance.

These sentences say what the instance holds. That it holds nothing more, so that the names of the form `outer/inner/x` are exactly the names `inner/x` of the body renamed under `outer`, follows from [MOD-010]: the renamed body holds exactly the body's places and transitions, each renamed. The third sentence takes for granted that every port of the definition names a place of its body and every channel a transition of its body, which the subnet builder ([MOD-006]) and `fromNet` ([MOD-014]) check.

**Acceptance Criteria:**
1. A subnet `S` containing a composed instance of `T` (instantiated with prefix `inner`), instantiated with prefix `outer`, produces names of the form `outer/inner/<original>`.
2. The names of the form `outer/inner/x` in the doubly-prefixed instantiation are exactly the names `inner/x` that the body of `S` holds, each renamed under `outer`, which is `x` renamed under the concatenated prefix `outer/inner`. An instantiation of `T` with the prefix `outer/inner` itself is rejected ([MOD-010]).
3. Per-instance state isolation per [MOD-012] holds at every nesting level.

**Depends on:** [MOD-010], [MOD-012], [MOD-014], [MOD-020], [MOD-021]
**Test derivation:** Build subnet `T` with internal place `x`. Build subnet `S` that composes `T` instance with prefix `inner`. Instantiate `S` with prefix `outer`; verify `outer/inner/x` is among the renamed place names.

---

#### MOD-014: SubnetDef.fromNet retrofit utility

**Priority:** MUST
**Kind:** B

Implementations MUST provide a utility `fromNet(net, iface)` that constructs a subnet definition from an existing closed `PetriNet` plus an interface declaration whose ports and channels expose places and transitions of that net. This allows pre-existing nets to be wrapped as reusable subnet fragments without rebuilding them. It is also how a subnet definition whose body holds a composed instance is built, which nested instantiation needs ([MOD-013]).

The retrofit utility MUST validate the interface against the supplied net per [MOD-006] (port places exist, channel transitions exist, names unique). The net is already built, so the body rejection of [MOD-006] (case 5) does not arise. A net that declares terminal places ([EXEC-042]) is accepted by `fromNet` and refused when the definition is instantiated ([MOD-010]).

As in [MOD-006], a channel over a transition of the net is accepted and a channel whose transition has the name of no transition of the net is rejected. Whether a channel over a second transition object that has the name of a net transition is accepted is implementation-defined: Java and TypeScript compare transition objects and reject it, Rust and Python compare names and accept it. After a composition the net holds rewritten transitions, so a channel exposes the transition taken from the net.

An interface holds at most one port and at most one channel of each name in every implementation, because the interface builder rejects a second declaration of a name; `fromNet` checks the names again. Port names and channel names are two namespaces, as in [MOD-006].

*If* a port of the interface exposes a place that is not a place of the net, *then* `fromNet` *shall* fail.

*If* a channel of the interface exposes a transition whose name is not the name of a transition of the net, *then* `fromNet` *shall* fail.

*If* two ports of the interface have the same name, *then* `fromNet` *shall* fail.

*If* two channels of the interface have the same name, *then* `fromNet` *shall* fail.

*When* every port of the interface exposes a place of the net, every channel exposes a transition of the net, and no two ports and no two channels have the same name, `fromNet` *shall* succeed.

*When* `fromNet` succeeds, the subnet definition *shall* have the net's name, the net's places, transitions and terminal places as its body, with the transitions in the net's order, and the given ports and channels as its interface.

*When* `fromNet` fails, the error message *shall* contain the name of a port or channel that meets one of the four rejection cases above.

**Acceptance Criteria:**
1. `fromNet(net, iface)` produces a subnet definition whose body equals the supplied net (modulo immutability semantics).
2. The interface validation rules of [MOD-006] apply.
3. The resulting subnet definition is unparameterised (its parameter type is the implementation unit/void type).

**Test derivation:** Build a `PetriNet` with places `a`, `b`; call `fromNet(net, iface{port: in -> a})`; verify the resulting subnet exposes port `in` over place `a`.

---

## Composition

#### MOD-020: Composition Operation (port mapping by structural rewrite)

**Priority:** MUST
**Kind:** B

The enclosing net's builder MUST support a `compose(instance, bindings)` operation that integrates a module instance into the enclosing net by **structural rewriting**:

1. Each binding maps an interface port name (resolved on the instance) to a caller-side `Place<T>`.
2. For every binding `(portName -> callerPlace)`: the instance's renamed port place is substituted with the caller place at every arc in the instance's renamed body.
3. Every place an arc of a rewritten instance transition names is added to the enclosing builder; an internal place that no arc names is not added.
4. Every transition of the instance's renamed body that no channel binding names (with rewritten arcs) is added to the enclosing builder; a transition that a channel binding names is replaced by its merge with the caller-side transition ([MOD-021]).
5. Composition is **eager**: the rewrite happens at compose time, not at build, executor compile, or run time. The enclosing builder's place and transition sets reflect the composed structure immediately after `compose(...)` returns.

The result of composition over the enclosing builder MUST be observationally indistinguishable from a hand-written flat net containing the same places, transitions, and arcs.

Within a single `compose(instance, bindings)` call, every interface port appears in the bindings at most once. Re-binding the same port name (whether to the same caller place or a different caller place) within one `compose(...)` call is a compose-time error; the error message MUST name the port. Symmetrically, the same caller-side `Transition` appears as the target of at most one channel binding within a single `compose(...)` call; re-binding a caller transition to two channels of the same instance in one call is a compose-time error naming the caller transition and both channels (no runtime enforces it yet, RD-11; see also [MOD-021]).

**Port-binding collision.** Two *different* ports of one instance MAY be bound to the same caller place. When that substitution would give one transition of the instance two input arcs on the caller place (the transition consumed from both ports), composition MUST reject the call at compose time, before the rewritten transition is rebuilt, with an error naming the instance prefix, a port exposing each of the two places (in either order), the caller place and the transition, e.g.

```
ports 'a' and 'b' of instance 's' are both bound to host place 'X'; transition 's/join' would consume from 'X' through two input arcs. Bind them to distinct places or use one port.
```

Without this check the rebuild would fail on [CORE-030] AC3 with a message that names only the rewritten transition, not the binding that caused it. When several pairs of bound ports collide on one transition, the error names one of the pairs.

The output side has the same shape. When the substitution would make one **AND branch** of a transition's output spec name the caller place twice (the transition wrote both ports in one branch), composition MUST reject the call at compose time with an error naming the instance prefix, a port exposing each of the two places (in either order), the caller place and the transition, e.g.

```
ports 'a' and 'b' of instance 's' are both bound to host place 'X'; transition 's/split' would produce into 'X' twice in one AND branch. Outputs are sets (IO-015); bind them to distinct places or use one port.
```

and not with the generic [IO-011] rejection the rebuild would otherwise raise. A branch is taken after flattening nested `And`s, as in [IO-011]. Two ports that land in **different** `Xor` alternatives are not a port-binding collision, because each alternative still names the place once. *If* the substitution makes two distinct alternatives claim the same set of places, such as `Xor(a, b)` becoming `Xor(X, X)`, *then* rebuilding the transition *shall* fail with the [IO-012] ambiguity message, which names the transition, the two output branches and the places.

Other effects of binding two ports to one place (an input and an output, an input and an inhibitor) are unchanged: they are legal arcs with their usual semantics. Binding an input port and a read port of one transition to one place makes the rebuilt transition fail with the [EXEC-012] message. The checks apply wherever [MOD-020] bindings are processed, so the auto-bound form of [MOD-024] is covered too.

In the sentences below, two different bound port places of one instance, both bound to one caller place, are an *input collision* of an instance transition when it has an input arc on each of them, and an *output collision* of it when one AND branch of its output specification names both. A call is *coherent* when any two of its port bindings whose ports expose one renamed place bind it to one caller place; the sentences below that say coherent claim nothing about any other call ([MOD-003]). A call is *plain* when no caller place it binds is a place that an instance transition names, no instance transition has two input arcs on one place, and no AND branch of an instance transition's output specification names one place twice. A call *passes the binding checks* when it binds every port at most once, binds only ports the instance declares, binds every port to a caller place of the port's token type ([MOD-022]), binds every channel at most once, binds only channels the instance declares and whose transition is a transition of the instance, and binds no two channels to one instance transition. A call *meets the caller obligations* when the instance's transitions and the caller-side transitions of its channel bindings have pairwise distinct names, no caller-side transition is a transition of the enclosing builder, and no caller-side transition names a bound port place of the instance.

*When* a coherent `compose(instance, bindings)` call that meets the caller obligations succeeds, the enclosing builder *shall* hold its earlier transitions followed by one transition per instance transition, among them, in the instance's order, every instance transition that no channel binding names with each bound port place replaced by its caller place in every arc and in the output specification and its name, timing, priority and action unchanged, and, for every channel binding, the [MOD-021] merge of its caller-side transition with the instance transition it names after the rewrite, and its places *shall* be its earlier places and the places its new transitions name.

*If* one `compose(...)` call binds a port name more than once, *then* the call *shall* fail with an error naming a port it binds more than once.

*If* a `compose(...)` call binds a port name that the instance does not declare, *then* the call *shall* fail.

*If* a coherent `compose(...)` call gives a transition of the instance an input collision, *then* the call *shall* fail.

*If* a coherent and plain `compose(...)` call passes the binding checks, an instance transition `t` has an input collision and no output collision, every instance transition before `t` has no collision and passes the checks of the transition builder after the rewrite, and no instance transition after `t` has a collision, *then* the call *shall* fail with the input collision message above, naming the instance prefix, a port exposing each of two places on which input arcs of `t` collide, in either order, their caller place and `t`.

*If* a coherent `compose(...)` call gives a transition of the instance an output collision, *then* the call *shall* fail.

*If* a coherent and plain `compose(...)` call passes the binding checks, an instance transition `t` has an output collision and no input collision, every instance transition before `t` has no collision and passes the checks of the transition builder after the rewrite, and no instance transition after `t` has a collision, *then* the call *shall* fail with the output collision message above, naming the instance prefix, a port exposing each of two places that collide in one AND branch of the output specification of `t`, in either order, their caller place and `t`.

*If* a coherent and plain `compose(...)` call passes the binding checks and has no collision, every instance transition before a transition `t` passes the checks of the transition builder after the rewrite, and `t` after the rewrite does not, *then* the call *shall* fail with the transition builder's message for `t` after the rewrite.

*When* a coherent `compose(...)` call that meets the caller obligations passes the binding checks, has no collision, every instance transition passes the checks of the transition builder after the rewrite, and every channel merge of [MOD-021] succeeds, the call *shall* succeed.

*If* a `compose(...)` call binds a channel name more than once, binds a channel that the instance does not declare, binds a channel whose transition is not a transition of the instance, or binds two channels to one instance transition, *then* the call *shall* fail.

**Acceptance Criteria:**
1. Compose an instance with binding `port "out" -> callerPlace P`; verify that every arc in the renamed body that referenced the port's renamed place now references `P` directly.
2. Internal places of the instance that an arc of a rewritten transition names appear in the enclosing builder under their renamed (prefixed) names.
3. Transition count of the enclosing builder after a compose call without channel bindings equals (prior count) + (instance transition count).
4. Building the enclosing net produces a `PetriNet` whose structure is identical to a hand-written equivalent.
5. Re-binding the same port name twice in a single `compose(...)` call (whether to the same caller place or different ones) is rejected at compose time with an error naming the port.
6. Binding the same caller-side transition to two distinct channels of one instance in a single `compose(...)` call is rejected at compose time with an error naming the caller transition and both channels.
7. Binding ports `a` and `b` of instance `s` to one caller place `X`, where instance transition `join` has an input arc on each port, is rejected at compose time with the port-binding collision message above, naming `a`, `b`, `s`, `X` and `s/join`. Binding the same two ports to `X` when no transition consumes from both is accepted.
8. Binding output ports `a` and `b` of instance `s` to one caller place `X`, where instance transition `split` declares `And(a, b)`, is rejected at compose time with the output collision message above, naming `a`, `b`, `s`, `X` and `s/split`, not with the generic [IO-011] message. With `Xor(a, b)` the same binding is rejected with the [IO-012] ambiguity message naming `s/split`, output branches 0 and 1, and `{X}`.

**Depends on:** [MOD-003], [MOD-010], [MOD-011], [MOD-021], [MOD-022], [CORE-030], [IO-011], [IO-012]
**Test derivation:** Build subnet with port `out`; compose with `out -> P`; export the resulting net and a hand-written equivalent; assert structural equivalence. Compose with `out -> P, out -> Q` in one call; verify rejection. Build a subnet whose transition `join` consumes from ports `a` and `b`; compose with `a -> X, b -> X`; verify rejection with the collision message. Repeat with a transition `split` producing `And(a, b)` (rejected, output message) and `Xor(a, b)` (rejected, [IO-012] message).

---

#### MOD-021: Channel Composition (transition merge: arc union + conflict resolution)

**Priority:** MUST
**Kind:** B

When a composition binding maps an interface channel to a caller-side `Transition`, the two transitions are **merged** into a single transition in the composed net. The merged transition combines:

1. **Arcs**: the union of all input, output, inhibitor, read, and reset arcs from both sides, with same-place arcs reconciled per the deduplication rule below.
2. **Timing** (per [TIME-001]): when one side's timing is `Immediate`, the merged timing is the other side's timing, so two `Immediate` sides give `Immediate`. Two equal timings collapse to that timing. Any other pair, two different timings neither of which is `Immediate`, MUST be rejected with an error naming the caller-side transition. That error MUST also name both timings, unless the two sides also break rule (d) below, in which case an implementation MAY report the rule (d) error instead. The merged timing is therefore always one of the two sides' timings.
3. **Priority**: the merged transition has the caller-side transition's priority; the instance-side priority is ignored.
4. **Action**: composed sequentially: caller-side action first, then instance-side action. The composed action is exposed to the executor as a single atomic firing: the executor sees one transition per [CORE-021].
5. **Identity**: the merged transition's name is the caller-side transition's name; the instance-side renamed channel transition is NOT separately added to the enclosing builder.

**Arc deduplication rule** (for clause 1): for every pair of arcs from the two sides targeting the same `Place` (by identity per [CORE-002]):
- (a) **Same arc type without a cardinality** (`Read`, `Inhibitor`, `Reset`): a same-place pair collapses to a single arc.
- (b) **Same arc type with a defined merge**: `Input` arcs on one place are reconciled by the canonical merge table below, not by rule (a). Output is one spec tree per transition rather than a per-place arc: the two sides' trees combine under a single outer `And` (clause 1), and a one-sided spec carries through unchanged. For example, when each side produces into `Q`, the merged `And(Q, Q)` names `Q` twice in one branch, which the transition builder rejects ([IO-011]), so the channel merge is rejected.
- (c) **Same arc type with no defined merge**: an `Input` pairing absent from the table MUST be rejected at compose time with the diagnostic below.
- (d) **Different arc types**: when both sides have arcs on one place and the two sides' sets of arc types on it (input, inhibitor, read, reset; an output is not counted) differ, for example an `Input` arc on `P` on one side and a `Reset` arc on `P` on the other, or `Read` + `Reset` on one side and `Read` alone on the other, the merge MUST be rejected at compose time. When the timings merge (clause 2), at most one side carries a ν-net match ([NU-060]) and the declared-place correspondences merge ([MOD-031]), the error MUST name the caller-side transition, such a place and each side's set of arc types on it, each set written as its arc-type names (`inhibitor`, `input`, `read`, `reset`) in alphabetical order, separated by a comma and a space, in square brackets, for example `[input]` or `[read, reset]`. Two sides declaring the *same* set of arc types on a place (e.g. `Read` + `Reset` on each side) are not a conflict: their same-type arcs pair up under rules (a)/(b).

**Canonical input-arc merge table.** This is the single normative statement of rule (b); [MOD-061] and [CORE-030] refer here rather than restating it. The table is symmetric.

| Left | Right | Merged |
|------|-------|--------|
| `one` | `one` | `exactly(2)` |
| `one` | `exactly(n)` | `exactly(n + 1)` |
| `exactly(n)` | `exactly(m)` | `exactly(n + m)` |
| `all` | `all` | `all` (idempotent collapse) |
| `atLeast(n)` | `atLeast(m)` | `atLeast(max(n, m))` |
| anything else | | **rejected** per rule (c) |

`one`/`exactly` sum because each side's demand is an independent fixed draw. `atLeast` does not sum: both sides take every available token, so the merged arc only has to carry the stricter minimum. `all` does not sum either: each side drains the place, so two `all` arcs merge to one `all` arc.

*When* two input arcs on one place are merged and each of them is `one` or `exactly`, the merged arc *shall* be `exactly` of the sum of their counts, where `one` counts 1.

*When* two `all` input arcs on one place are merged, the merged arc *shall* be `all`.

*When* two `atLeast` input arcs on one place are merged, the merged arc *shall* be `atLeast` of the larger of their two minimums.

*If* two input arcs on one place are merged and the pair is none of these three cases (each side `one` or `exactly`, both `all`, both `atLeast`), *then* the merge *shall* be rejected (rule (c)).

A rejection MUST name the seam, both cardinalities, and the place, in this shape:

```
<seam>: input arcs <a> and <b> collide on place '<p>' and have no additive merge (MOD-021 rule (c)). Use a single arc with exactly(n) / atLeast(n).
```

`<seam>` is `Fusion set '<name>'` ([MOD-061]) or `Channel composition '<name>'`; `<a>` and `<b>` render cardinality only (`one()`, `exactly(3)`, `all()`, `atLeast(2)`) with no place name embedded. Method spelling follows the host language (`at_least(n)` in Rust and Python).

The result is one merged `Transition` in the flat net; firing it consumes/produces tokens per the unioned arc set in a single atomic step per [EXEC-001].

In the sentences below, a *channel merge* merges a caller-side transition with the instance-side channel transition it is bound to, whose arcs the port bindings have already rewritten ([MOD-020]). The sentences cover a caller-side transition that was not added to the net builder before the compose call and has no arc on a port bound in the same compose call; for other caller-side transitions the implementations differ, and this requirement does not yet state the outcome.

*When* a channel merge succeeds, the merged transition *shall* have the caller-side transition's name and priority.

*When* a channel merge succeeds and neither side has two input arcs on one place, the merged transition *shall* have at most one input arc on each place: none where neither side has an input arc, an arc of the one side's cardinality where only one side has an input arc, and an arc of the cardinality the canonical input-arc merge table gives for the two where both sides have one.

*When* a channel merge succeeds, the merged transition *shall* have, for each of the arc types inhibitor, read and reset, one arc of that type on every place on which either side has an arc of that type, and no other arc of that type.

*When* a channel merge succeeds, the output specification of the merged transition *shall* be `And` of the caller-side specification and the instance-side specification, in that order, when both sides have one, the one side's specification when only one side has one, and none when neither side has one.

*When* a channel merge succeeds, the timing of the merged transition *shall* be the instance-side timing when the caller-side timing is `Immediate`, and the caller-side timing otherwise.

*When* a channel merge succeeds, the action of the merged transition *shall* be the caller-side action followed by the instance-side action.

*When* a channel merge succeeds, the merged transition *shall* pass the checks of the transition builder ([CORE-030], [IO-011], [IO-012], [EXEC-012]).

*If* neither side's timing is `Immediate` and the two timings differ, *then* the channel merge *shall* be rejected with a message that names the caller-side transition.

*If* neither side's timing is `Immediate`, the two timings differ, and the two sides' sets of arc types agree on every place on which both sides have an input, inhibitor, read or reset arc, *then* the channel merge *shall* be rejected with a message that names the caller-side transition and both timings.

*If* both sides have an input, inhibitor, read or reset arc on one place and the two sides' sets of arc types on that place differ, *then* the channel merge *shall* be rejected.

*If* the timings merge, at most one side carries a ν-net match ([NU-060]), the declared-place correspondences merge ([MOD-031]), and on some place both sides have an input, inhibitor, read or reset arc and the two sides' sets of arc types on it differ, *then* the channel merge *shall* be rejected with a message that names the caller-side transition, one such place and the two sides' sets of arc types on it, each set written as in rule (d).

*If* the timings merge, at most one side carries a ν-net match ([NU-060]), the declared-place correspondences merge ([MOD-031]), the two sides' sets of arc types agree on every place on which both sides have an input, inhibitor, read or reset arc, neither side has two input arcs on one place, and both sides have an input arc on a place for which the canonical input-arc merge table has no merge, *then* the channel merge *shall* be rejected with the rule (c) diagnostic for such a place and its two arcs, the caller-side arc first, with the seam `Channel composition '<name>'` where `<name>` is the caller-side transition's name.

*When* the timings merge, at most one side carries a ν-net match ([NU-060]), the declared-place correspondences merge ([MOD-031]), the two sides' sets of arc types agree on every place on which both sides have an input, inhibitor, read or reset arc, neither side has two input arcs on one place, every place where both sides have an input arc has a merge in the canonical input-arc merge table, and the transition builder accepts every transition that these sentences allow as the merged transition, the channel merge *shall* succeed.

**Acceptance Criteria:**
1. Bind a caller transition `T` (with arcs `[in: P]`, `out: Q`, `Immediate`, priority 0) to a channel transition `C` (with arcs `[in: R]`, `out: S`, `Immediate`, priority 0). The composed net contains one transition with input arcs from both `P` and `R`, output arcs to both `Q` and `S`, `Immediate` timing.
2. Bind two transitions with different non-`Immediate` timings, for example `Delayed(100ms)` and `Deadline(50ms)`; verify the compose call is rejected with a message identifying both timings.
3. Bind a caller transition with `Immediate` timing to a channel transition with `Delayed(100ms)`; verify the merged timing is `Delayed(100ms)`. Bind two transitions that are both `Window(10, 100)`; verify the merged timing is `Window(10, 100)`. Bind caller `Deadline(100ms)` to instance `Delayed(50ms)`; verify the compose call is rejected.
4. The merged transition's action runs the caller-side action then the instance-side action sequentially within one firing; observable token movement is atomic from the executor's perspective.
5. After build and run, the executor invokes the merged transition once per fire (not twice).
6. **Arc deduplication, merge table:** bind a caller transition with `Input(One) -> P` to a channel transition with `Input(One) -> P` on the same caller place `P`; verify the merged transition has a single `Input(Exactly(2)) -> P` arc. Verify the remaining rows too: `All` + `All` collapses to `All`, and `AtLeast(1)` + `AtLeast(3)` merges to `AtLeast(3)` (not `AtLeast(4)`).
7. **Arc deduplication, different types are rejected:** bind a caller transition with `Input -> P` to a channel transition with `Reset -> P`; verify the compose call is rejected with a message naming the caller-side transition, `P`, `[input]` and `[reset]`.
8. **Arc deduplication, off-table pairings are rejected:** bind a caller transition with `Input(One) -> P` to a channel transition with `Input(All) -> P`; verify the compose call is rejected with the diagnostic shape above, naming the seam, both cardinalities, and the place.
9. **Token timestamp on merged production:** when the merged transition fires and produces a token to a place that is itself a port-merge or fusion target, the produced token is stamped as any token the executor creates is ([CORE-011]) and deposited at the tail of its place as the tokens of any admitted completion are ([EXEC-020], [CONC-003]). Tokens that distinct firings of one or more merged transitions produce into one place keep the order in which the executor admits the completions of those firings ([CONC-003]). The merged transition emits a single `TokenAdded` event per produced token (cf. EVT-011), not one per side of the merge.

**Depends on:** [MOD-005], [MOD-020], [MOD-031], [CORE-011], [CORE-021], [CORE-030], [TIME-001], [IO-011], [IO-012], [EXEC-001], [EXEC-012], [EXEC-020], [CONC-003], [NU-060]
**Test derivation:** Compose two transitions with non-overlapping arcs; verify the resulting flat net has one transition combining all arcs. Compose with two different non-`Immediate` timings; verify rejection. Compose an `Immediate` side with a timed side; verify the merged timing is the timed side's. Compose with two `one` or `exactly` input arcs on the same place; verify the counts are summed. Compose with two `atLeast` input arcs on the same place; verify the larger minimum is kept. Compose with `one` and `all` input arcs on the same place; verify rejection. Compose with conflicting arc types on the same place; verify rejection.

---

#### MOD-022: Type Compatibility at Compose

**Priority:** MUST
**Kind:** B

A port binding `port(name, T) -> callerPlace` is well-typed only when the port's declared token type and the caller place's token type are the same `T`. Where the binding is checked depends on the implementation's place identity:

1. In Java, place identity carries the token type. Every compose overload, the map overload with erased generics included, checks the port bindings when `compose` runs, before the collision check of [MOD-020] and before it rewrites anything. It rejects the call at the first binding it meets that names an unknown port or whose caller place has another token type than the port's place. For a binding of another token type the message names the port, the token type of the port's place and the token type of the caller place.
2. In Rust, TypeScript and Python, place identity does not carry the token type, and compose checks no token type. No binding API relates the port's declared token type to the caller place's type. Rust's `bind_port::<T>` and TypeScript's `bindPort<T>` take `T` from the caller place they are given, so a wrong-type binding is no compile-time error there. Python's compose takes a mapping from port names to places. In none of the three is a wrong-type binding rejected at compose. The token type of a caller place is then a property of the caller's place handle, and the typing invariant of [CORE-003] is premised on compatible emissions.

Channel bindings have no token-type check at the channel level (transitions are not typed); arc-level type compatibility falls out from the underlying place token types per [CORE-003].

*Where* place identity carries the token type (Java), *if* a compose call binds no port twice and binds a port to a caller place whose token type differs from the token type of the port's place, *then* the compose call *shall* fail.

*Where* place identity carries the token type (Java), *if* a compose call binds no port twice, binds only ports of the interface and binds some port to a caller place of another token type, *then* the error message of its failure *shall* name such a port, the token type of the port's place and the token type of the caller place.

*Where* place identity carries the token type (Java), *when* a compose call binds no channel, binds no port twice, binds only ports of the interface, binds each port it binds to a caller place of the token type of the port's place, sends no two different port places that one transition consumes from or that one output branch of a transition names to one caller place, and every transition rewritten through the bindings passes the transition builder's checks, the compose call *shall* succeed.

**Acceptance Criteria:**
1. `port("in", String) -> Place<String>` binding composes successfully.
2. In Java, a `port("in", String) -> Place<Integer>` binding is rejected at compose, through the typed binding overload and the map overload alike, with a message containing `port 'in'`, `String` and `Integer`.

**Depends on:** [CORE-003], [MOD-011], [MOD-020]
**Test derivation:** Java: bind a port to a caller place of another token type, through the typed overload and through the map overload; verify both calls are rejected with a message containing the quoted port name (`port 'in'`, since `in` alone occurs inside other words) and both type names. Every language: bind a port to a caller place of its own token type; verify the composition succeeds.

---

#### MOD-023: Composition Produces Flat Net

**Priority:** MUST
**Kind:** B

After all `compose(...)` (and `fuse(...)` per [MOD-061]) calls have been made on a builder, `build()` MUST produce a `PetriNet` indistinguishable from a hand-written flat net that has the same places, transitions, arcs, timing, priority, and actions. Two records a composed net may carry sit beside that structure and are not part of it: the subnet membership of [MOD-026], which only direct composition records, and the declared-to-actual correspondence of [MOD-031], through which an action resolves the places its subnet declared where a hand-written action names the actual places.

In particular, downstream consumers, namely the executor (CONC, EXEC), the event subsystem (EVT), the verifier (VER) and the exporter (EXP), MUST require no awareness of composition structure to operate on the composed net, except that the exporter MAY read the subnet membership of [MOD-026] to draw subnet clusters ([MOD-040]). Compiled net representations per [CONC-007], [CONC-020] MUST be constructed identically whether the source net was composed from subnets or hand-written, provided the hand-written net declares its places in the order the composed net holds them.

*When* `build()` succeeds, every transition of the built net *shall* pass the checks of the transition builder ([CORE-030], [IO-002], [IO-004], [EXEC-012], [IO-011] to [IO-014]), whichever `compose(...)`, `fuse(...)` or other builder calls produced it.

*When* `build()` succeeds, a new builder on which the places of the built net are declared, its transitions are added by hand in the same order with the same name, arcs, output specification, timing, priority and action and no correspondence ([MOD-031]), and its terminal places ([EXEC-042]) are declared *shall* build a net with the same transitions in the same order, the same places, each listed as often, in any order, and the same set of terminal places.

*When* `build()` succeeds and no `compose(...)` call binds a channel ([MOD-021]), the built net *shall* hold one transition for each transition added by hand and for each transition of a composed instance or of a directly composed subnet, in the order of the calls and, within one call, in the order of the subnet, each with the name, timing, priority and action it was added with.

**Acceptance Criteria:**
1. Build the composed net and a hand-written equivalent net that declares its places in the order the composed net holds them; their compiled representations have identical place index, transition count, arc topology, bitmap masks, and timing arrays.
2. Running both nets, with the hand-written net's actions naming the actual places where the composed actions resolve the places their subnet declared ([MOD-031]), under the same executor with the same initial marking produces identical event sequences and final markings.
3. When the composed net carries no subnet membership ([MOD-026]), exporting both nets produces byte-equal DOT modulo group ordering; a directly composed net may differ from its hand-written equivalent by the subnet clusters drawn from its membership ([MOD-040]).
4. Running verification on both nets produces identical results.

**Depends on:** [MOD-020], [MOD-021], [CONC-007], [EXEC-001]
**Test derivation:** Build a composed net `N1` and a hand-written equivalent `N2` whose actions name the actual places; run both with identical initial markings; assert identical event sequences and final markings.

---

#### MOD-024: Identity-Default Port Inference (auto-compose)

**Priority:** SHOULD
**Kind:** B

The enclosing net's builder SHOULD support a single-argument `compose(instance)` overload that auto-binds every interface port declared on the subnet to the host place carried on that port's declaration. For each `port` returned by `instance.def().iface().ports()` the implementation MUST contribute a binding `(port.name() → port.place())`; the resulting binding map MUST be processed identically to an explicit `compose(instance, map)` call per [MOD-020]. The result MUST therefore satisfy [MOD-023] (composition produces a flat net) with no observable difference from the explicit form.

When the subnet declares no interface ports, the implementation MAY additionally infer bindings by walking the instance's renamed body and matching each renamed place against the host builder's place set, probed by the place's original (un-prefixed) identity. Body places that do not match stay private under their prefixed names per [MOD-010] and [MOD-012]. The probe identity SHOULD use the implementation's existing `Place` equality (per [CORE-002]); implementations whose `Place` equality is name-only MAY still implement the body-inference path but MUST document the more permissive matching contract in their API surface.

Channels are NOT auto-bound. If the subnet's interface declares any channel, `compose(instance)` MUST raise an error naming the channels and directing the caller to the explicit-binding `compose(instance, bindings)` overload per [MOD-021]. Transition identity is too delicate for inference. Caller code is expected to think about which caller-side transition fuses with which channel.

The single-argument form is **additive** sugar over [MOD-020]; it does NOT replace the explicit-binding overloads. Callers SHOULD use the Consumer/Map overloads when (a) they need to rewire a port to a host place other than the one the SubnetDef declared, (b) the subnet has any channel, or (c) the subnet defines reusable ports whose host targets differ across instances.

*When* `compose(instance)` is called on an instance whose subnet declares at least one port and no channel, the builder *shall* give the same result as `compose(instance, bindings)` with each declared port bound to the place on that port's declaration, the same rejection included.

*If* the subnet of an instance passed to `compose(instance)` declares a channel, *then* `compose(instance)` *shall* fail with an error that names every channel the subnet declares.

*Where* the builder infers bindings for a subnet without ports, *when* `compose(instance)` succeeds on an instance whose subnet declares no port and no channel and whose transitions have pairwise distinct names, the builder *shall* keep its transitions and add the instance's transitions in order, each with every arc and output place on a renamed body place `p/x` moved to `x` when the builder held `x` at the call, by the implementation's `Place` equality, every other place kept, its name, timing, priority and action unchanged and its declared-to-actual place correspondence ([MOD-031]) moved the same way, *shall* add to its places exactly the places those transitions name, and *shall* leave its terminal places, retired ports, subnet membership and fusion sets as they were.

*Where* the builder infers bindings for a subnet without ports, *when* `compose(instance)` is called on an instance whose subnet declares no port and no channel and whose transitions have pairwise distinct names, `compose(instance)` *shall* succeed exactly when every instance transition, with each renamed body place `p/x` moved to `x` when the builder holds `x`, passes the transition builder's checks.

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

#### MOD-025: Direct Composition (compose a subnet without instantiation)

**Priority:** MUST
**Kind:** B

The enclosing net's builder MUST support a direct-composition operation that
integrates a subnet **definition** into the enclosing net **without
instantiation** — without the prefix-renaming of [MOD-010]. The operation takes
a subnet definition (not a module instance) and:

1. Adds every transition of the subnet's body net to the enclosing builder
   under its **original** (un-prefixed) name.
2. Adds every place of the subnet's body net under its **original** name.
   Places merge purely by name equality: a subnet body place whose name equals
   an enclosing-net place is the same place in the composed flat net.
3. Arc topology, timing, priority, and actions of every body transition are
   preserved (actions shared by reference per [MOD-030]).
4. Composition is **eager** per [MOD-020].

Direct composition is **order-independent**: composing the same set of subnets
into one builder in any order MUST produce the same places, the same transitions
and the same arcs, because merging is by name equality against the builder's
place set (per [CORE-002]) and not by a probe of the builder's place set at call
time. This distinguishes it from the body-inference fallback of [MOD-024], which
is order-sensitive. The order in which the places and the transitions are
declared follows the order of the calls; for the transitions that order is the
last tie-break of the ready order ([EXEC-002]).

Direct composition is the appropriate mode for wiring a subnet into a host as a
single shared copy. For multiple independent copies — each with isolated
per-instance state per [MOD-012] — callers MUST use instantiate(prefix) per
[MOD-010] followed by composition of the resulting instance per [MOD-020]/[MOD-024].

**Transition name collisions.** If a body transition's name equals a transition
already present in the enclosing builder, direct composition MUST be rejected at
compose time with an error naming the transition and both nets, directing the
caller to the instantiation path for multi-copy use.

**Place type conflicts.** A body place whose name equals an enclosing-net place
but whose token type differs is a type error. Implementations whose place
equality carries the token type ([CORE-002]) MUST reject this at compose time
naming the place and both token types. Implementations whose place equality is
name-only MAY accept it; they MUST document the resulting name-only merge
contract in their API surface (same carve-out as [MOD-024]).

**Channels.** Direct composition does NOT bind channels. If the subnet's
interface declares any channel, the operation MUST raise an error naming the
channels and directing the caller to instantiate(prefix) + the explicit-binding
composition overload per [MOD-021]. Interface ports are advisory only ([MOD-004])
and impose no additional behaviour: a port's underlying body place merges by
name like any other body place.

The result MUST satisfy [MOD-023]. Direct composition is additive; it does NOT
replace instantiate + compose.

*When* direct composition of a subnet definition into an enclosing builder succeeds, the builder *shall* hold its earlier transitions followed by the body's transitions in the body's order, each unchanged and under its original name, and its earlier places together with every body place and every place a body transition names, a body place equal to a place it already holds being that place, no place added twice, and nothing else of the builder changed but the subnet membership of [MOD-026].

*If* a body transition's name is the name of a transition already in the enclosing builder, *then* direct composition *shall* fail at the call.

*If* the subnet definition declares no terminal place and no channel and exactly one name of its body transitions is the name of a transition already in the enclosing builder, *then* the error *shall* name that transition and the subnet definition.

*If* the interface of a subnet definition declares a channel, *then* direct composition of that definition *shall* fail at the call.

*Where* place identity carries the token type ([CORE-002]), *if* a body place has the name of a place the enclosing builder holds and a different token type, *then* direct composition *shall* fail at the call.

*When* a subnet definition that declares no terminal place ([EXEC-042]) and no channel is composed directly into an enclosing builder that holds no transition with the name of a body transition and, where place identity carries the token type, no place with the name of a body place and a different token type, direct composition *shall* succeed.

*If* two subnet definitions that declare no terminal place, and whose body transitions name only their own body places, are composed directly one after the other into one builder and both calls succeed, *then* composing them in the other order *shall* also succeed in both calls and give a builder with the same places and the same transitions, each with its arcs, timing, priority and action.

*If* the body of a subnet definition declares a terminal place ([EXEC-042]), *then* direct composition of that definition *shall* fail at the call.

**Acceptance Criteria:**
1. Direct-composing a subnet with body place `output` into a host declaring
   `output` produces a flat net with a single `output` place; every body arc
   referencing `output` references the host place.
2. Body transitions appear under their original names; no `prefix/` separator
   appears in any name introduced by direct composition.
3. Direct-composing the same two subnets in opposite orders produces flat nets
   that are observationally identical (place set, transition set, arc topology).
4. Direct-composing a subnet whose body transition name collides with a
   transition already in the builder is rejected at compose time, naming the
   transition and pointing at the instantiation path.
5. Direct-composing a subnet declaring any channel is rejected, naming the
   channels and pointing at the instantiation + explicit-binding path.
6. (Token-typed-place implementations) Direct-composing a subnet with body place
   `x` of one token type into a host with `x` of a different type is rejected at
   compose time naming the place and both types.
7. An empty subnet direct-composes as a no-op.
8. Direct composition and instance composition MAY be mixed in one builder;
   un-prefixed and `prefix/` names coexist without collision.
9. Direct composition followed by build() is observationally indistinguishable
   from a hand-written flat net for the same wiring, per [MOD-023].

**Depends on:** [MOD-001], [MOD-020], [MOD-023], [CORE-040]
**Test derivation:** Build a producer subnet with body place `output`;
direct-compose it into a host declaring `output`; assert one `output` place and
that `produce`'s output arc references the host place. Direct-compose producer
then consumer, and consumer then producer; assert structurally identical flat
nets. Direct-compose two subnets sharing a transition name; assert rejection.
Direct-compose a channel-declaring subnet; assert rejection naming the channel.

---

#### MOD-026: Subnet-Membership Metadata for Direct Composition

**Priority:** SHOULD
**Kind:** B

Direct composition per [MOD-025] erases the `prefix/` name segments that
[MOD-040] and [EXP-016] rely on to reconstruct subnet clusters. To keep
cluster-aware export available for directly-composed nets, the builder SHOULD
record **subnet-membership metadata** on the net it builds: a mapping from node
name (place or transition) to the name of the owning subnet.

The mapping is resolved from the per-`compose(SubnetDef)` contributions:

1. Every body place and every body transition of a `compose(SubnetDef)` call is
   recorded, by name, as contributed by that subnet (its definition name per
   [MOD-001]), also when the builder already held a place of that name. Subnets
   are told apart by their recorded names. A call that fails records nothing.
2. A node contributed by **exactly one** subnet maps to that subnet.
3. A place contributed by **two or more** subnets is a shared rendezvous place
   with no single owner and MUST be **absent** from the mapping (it renders
   outside any cluster). A transition cannot be multiply-contributed: the
   transition-name-collision rejection of [MOD-025] forbids it.
4. A node of a net not built via direct composition is absent from the mapping.
   Instance composition per [MOD-020] and [MOD-024] records no membership: those nodes carry
   their `prefix/` names and cluster via [MOD-040]'s name-based detection. A
   caller that wants one answer for both kinds of composition asks the net's
   `subnetOf(name)` accessor ([MOD-040]), which reads this mapping first and
   falls back to the instance prefix; the mapping itself stays empty for
   instance-composed nodes.

A subnet definition name containing the `/` separator MUST be sanitized (each
`/` replaced by `_`) before it is recorded, so a membership value never triggers the
nested-cluster splitting that [MOD-040] applies to `/`-bearing prefixes.

The mapping is immutable, carried on the built net, and observability-only: it
does NOT affect execution, marking, or any property of [MOD-023] (the net is
still flat). Action binding per [CORE-042] rebuilds transitions but preserves
their names, so the mapping survives a re-bind unchanged. Fusion per [MOD-061]
removes the non-canonical places it merges away; their membership entries MUST
be dropped so the mapping names only nodes that still exist.

*When* a `compose(SubnetDef)` call succeeds, the builder *shall* record each body place and each body transition of the subnet definition, by name, as contributed by that subnet under the definition's name with each `/` replaced by `_`.

The builder *shall* record contributions only in `compose(SubnetDef)` calls.

*When* a node name is recorded as contributed by exactly one subnet, the resolution of the recorded contributions *shall* map that node name to that subnet.

*If* a node name is recorded as contributed by two or more different subnets, *then* the resolution *shall* have no entry for that node name.

*If* a node name is recorded as contributed by no subnet, *then* the resolution *shall* have no entry for that node name.

*When* a build succeeds, the membership mapping of the built net *shall* be the resolution of the contributions the build recorded, except for the names of the places that fusion ([MOD-061]) removed.

*If* fusion removes a member place other than the first member of its fusion set, *then* the membership mapping of the built net *shall* have no entry for that member's name.

*When* a build succeeds, a build that differs from it only in the names of the subnet definitions it composes directly *shall* also succeed and give the same places, transitions, terminal places and transition correspondences ([MOD-031]).

*When* actions are bound to a built net ([CORE-042]), the net that binding returns *shall* carry the same membership mapping.

**Acceptance Criteria:**
1. Direct-composing two subnets `A` and `B` records each private node under its
   subnet: a place or transition contributed only by `A` maps to `A`.
2. A place named identically in two directly-composed subnets whose recorded
   names differ is absent from the mapping.
3. A net not built via direct composition (flat, or instance-composed) has an
   empty membership mapping.
4. Direct-composing the same subnets in opposite orders yields equal mappings.
5. Fusing away a non-canonical place removes its membership entry; the
   surviving canonical place keeps its own.
6. A subnet definition name containing `/` is recorded with `/` replaced.

**Depends on:** [MOD-025], [MOD-023], [MOD-001]
**Test derivation:** Direct-compose a producer subnet and a consumer subnet
sharing a place `pipe`; assert each subnet's private place/transition maps to
its subnet name and `pipe` is absent. Build a flat net; assert an empty
mapping. Direct-compose then fuse two places; assert the non-canonical place's
entry is gone.

---

#### MOD-027: References to Bound Ports

**Priority:** MUST
**Kind:** B

Instance composition ([MOD-020], and [MOD-024]'s auto-bound form) replaces a bound port's
renamed place with the caller place at every arc of the instance. After the call, the renamed
port place is not in the net. [MOD-011] still hands it out, though: `instance.port("in")` returns
the pre-binding place `answer/IN` whatever it was bound to. A host arc that names it (a reset
meant to clear the subnet's input, say) therefore names a fresh place that nothing connects to,
and the arc silently does nothing:

```
compose(answer, in -> A_IN)          // answer/IN is replaced by A_IN in every instance arc
host transition hub_kill: reset(answer.port("in"))   // names answer/IN, which no longer exists
```

The builder MUST remember every port place a composition **retired** this way: the renamed port
place, the caller place that replaced it, the port name and the instance prefix. A port bound to
a caller place of the identical identity (the implementation's `Place` equality, [CORE-002]) is
not retired, since nothing was replaced.

When the net is built, if any arc of any kind names a retired place (an input arc, any place
anywhere in an output spec's tree, a read, an inhibitor or a reset arc, under the implementation's
`Place` equality), `build()` MUST fail with an error naming the place, the port, the instance and
the caller place, and pointing at the caller place:

```
place 'answer/IN' is port 'in' of instance 'answer', bound to host place 'A_IN' at compose; reference 'A_IN' instead
```

The check runs at build, not at compose or at arc addition, so the outcome does not depend on
whether the offending arc was added before or after the `compose(...)` call. It is checked on the
net **after fusion** ([MOD-061]): an arc that named a fusion member now names the canonical place,
and the check sees that arc as the built net carries it. When two compositions retire the same
place, the first record is kept (set-if-absent), so the error names the binding that retired it
first. A net that merely
*declares* the retired place, without any arc naming it, is not rejected by this rule. Places
that direct composition ([MOD-025]) merges by name, body places merged by [MOD-024]'s
no-interface inference, and places [MOD-061] fuses away are not ports, and are not retired.

A retired place is recorded per builder: it is the builder that performed the composition that
rejects a reference to it. The record is not carried on the built net.

In the sentences below, a *retired place* is the renamed place of a port that a composition of the builder, `compose(instance, bindings)` or [MOD-024]'s auto-bound form, bound to a caller place other than that renamed place under the implementation's `Place` equality. A transition *after fusion* is the transition with its arcs and output specification rewritten as [MOD-061] rewrites them; on a builder without fusion sets it is the transition itself. The places a transition names are its input, inhibitor, read and reset places and the places of every branch of its output specification; the source of a forward output is an input place ([IO-014]).

*If* no composition of the builder binds one renamed place to two different caller places and a transition of the builder after fusion, one added to the builder or one a composition added, names a retired place in an arc of any kind or in its output specification, *then* `build()` *shall* fail, whatever the order in which the transition and the composition that retired the place were added.

*If* a transition that fusion rewrites without an input-arc collision, that passes the transition builder's checks before and after fusion, and that after fusion consumes from or reads no terminal place and names exactly one retired place, is added to a builder whose net builds and whose fusion sets share no place, before or after its other calls but after every auto-bound and direct composition ([MOD-024], [MOD-025]), and no composition of the builder binds one renamed place to two different caller places, *then* `build()` *shall* fail with the message `place '<place>' is port '<port>' of instance '<instance>', bound to host place '<caller>' at compose; reference '<caller>' instead`, where `<place>` is that retired place and `<port>`, `<instance>` and `<caller>` are the port, the instance prefix and the caller place of a binding by which the first composition that retired the place retired it.

*When* a transition that fusion rewrites without an input-arc collision, that passes the transition builder's checks before and after fusion, and that after fusion names no retired place and consumes from or reads no terminal place, is added to a builder whose net builds and whose fusion sets share no place, before or after its other calls but after every auto-bound and direct composition, `build()` *shall* still succeed.

*When* one more place, a retired place included, is declared on a builder whose net builds, before or after its other calls but after every auto-bound and direct composition, `build()` *shall* still succeed.

*When* a `compose(instance, bindings)` call without channel bindings takes the place of a direct composition ([MOD-025]) of the instance's transitions rewritten through its bindings on a builder whose net builds, with no auto-bound or direct composition after it, and the call binds every port at most once, only ports the instance declares, each port to a caller place of its port's token type ([MOD-022]) and one renamed place to one caller place only, the instance's transitions have distinct names and no input or output collision under the bindings ([MOD-020]), and no transition of that net names a place the call retires, `build()` *shall* still succeed.

**Acceptance Criteria:**
1. Compose instance `answer` with `in -> A_IN`, then add a host transition with a reset arc on
   `answer.port("in")`: `build()` fails with the message above.
2. The same outcome when the host transition is added before the `compose(...)` call.
3. The same outcome for an input, output (including a place inside an XOR branch), read or
   inhibitor arc on the retired place.
4. Referencing `A_IN` instead builds, and the reset clears the place the instance consumes from.
5. Binding a port to a caller place equal to the port's own renamed place retires nothing; arcs
   naming it build.
6. An unbound port's renamed place is not retired; arcs naming it build.
7. The check sees the fused net: a host arc naming the retired place `answer/IN` builds when a
   fusion set ([MOD-060]) lists `answer/IN` as a non-canonical member, because after fusion the
   arc names the canonical place. Conversely, when the retired place is the **canonical** member,
   an arc on another member is fused onto it and `build()` fails. Every implementation gives both
   outcomes.

**Implementation notes:**
- Java: `PetriNet.Builder` records the retired ports in `compose(...)` and checks in `build()`.
- TypeScript: `PetriNetBuilder` records them in `compose(...)` and checks in `build()`.
- Rust: `PetriNetBuilder` records them in `compose(...)` and checks in `build()`, which panics
  like its other structural checks.
- Python: inherits the Rust check; building the `Net` raises `StructureError`.

**Depends on:** [MOD-010], [MOD-011], [MOD-020], [MOD-024], [MOD-061], [CORE-002], [CORE-040]
**Test derivation:** A subnet with input port `in` feeding a transition; instantiate as `answer`;
compose with `in -> A_IN`; add a host transition `hub_kill` resetting `answer.port("in")`, once
before and once after the compose; both builds fail with the message. Replace the reference with
`A_IN`; the build succeeds.

---

## Action Binding

#### MOD-030: Action Binding Per Instance (share-by-default, override via bindActions)

**Priority:** MUST
**Kind:** F

Actions associated with transitions in a subnet definition's body are carried through instantiation **by reference**, not by copy: by default, two instances of the same subnet definition share the same action object for each transition.

A module instance MUST support per-instance action override: `instance.bindActions(mapping)` produces a derived instance whose specified transitions (named by their **original**, pre-prefix names) carry the supplied actions instead of the shared defaults. Transitions not named in the override mapping retain the shared default action.

The override mechanism is per-instance: overriding actions on instance A does NOT affect instance B of the same subnet definition.

**Composition of multiple `bindActions` calls — last-wins replace, not chain.** Each call to `bindActions` returns a derived instance whose action map is the parent instance's action map with the per-transition entries from this call **overwriting** any existing entry for the same transition (entries for transitions not named in the call are inherited unchanged from the parent). Successive `bindActions` calls on the same instance compose left-to-right in derivation order: if `inst1 = inst0.bindActions({"t": A})` and `inst2 = inst1.bindActions({"t": B})`, then `inst2`'s `t` carries action `B`, not a sequential composition of `A` and `B`. A transition therefore carries **exactly one** action at composition time, regardless of how many `bindActions` calls produced the instance. Each `bindActions` call returns a new derived instance and MUST NOT mutate the receiver.

This requirement extends [CORE-042] (action binding separation) into the modular composition layer: subnets remain structure-only by default, with per-instance behavior layered on at composition time.

*When* `bindActions` is called on a module instance with prefix `p` and a mapping in which every key `k` names a transition `p/k` of the instance, the call *shall* return a derived instance.

*When* `bindActions` on a module instance returns a derived instance, the derived instance *shall* have the prefix, the places, the interface and the port and channel handles of the receiver and, for each transition of the receiver, in the same order, a transition with the same name, arcs, output specification, timing, priority and declared-to-actual place correspondence ([MOD-031]).

*When* `bindActions` on a module instance with prefix `p` returns a derived instance and the mapping maps a key `k` to an action, the transition `p/k` *shall* carry that action in the derived instance.

*When* `bindActions` on a module instance with prefix `p` returns a derived instance, a transition whose name is not `p/k` for any key `k` of the mapping *shall* carry in the derived instance the action it carried in the receiver.

Whether a call whose mapping holds a key `k` for which the instance has no transition `p/k` returns a derived instance (Rust, Python: the key is ignored) or is rejected (Java, TypeScript: an error naming the key) is not specified.

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

#### MOD-031: Action Place Resolution under Composition (declared → actual correspondence)

**Priority:** MUST
**Kind:** F

A transition action MAY reference places by their **declared** identity — the place constants visible when the subnet body was authored, *before* instantiation ([MOD-010]) and *before* port binding ([MOD-020]). Instantiation and port binding rewrite the transition's **arcs** to the renamed / bound places ([MOD-010] clause 5, [MOD-021]) but carry the action through **by reference**, unchanged ([MOD-030]). Without a resolution rule, an action that hardcodes `ctx.input(declared)` / `ctx.output(declared, …)` would consult the *declared* place while the context's allowed-place set is built from the *rewritten* arcs — the two place-spaces diverge and the action fails its declared-place check.

To close that asymmetry, each transition carries a **declared → actual place correspondence** established at compose time. Where an implementation resolves declared places in its context operations, in the context API or in a binding adapter (see the MAY paragraph below), the action-facing context operations `input`, `inputs`, `inputToken` (where it exists), `read` and `output` (all overloads) MUST resolve a key place through this correspondence to the actual composed place **before** the declared-set check and before reading or writing the token store. Place-set *discovery* (`inputPlaces` / `outputPlaces`) MUST continue to return the **actual** composed places, so port-agnostic actions (which discover places from the context) are unaffected and the two action styles coexist, except on a discovered place that is also, by the implementation's place equality ([MOD-024]), a declared place of the same transition that the correspondence resolves to another place, for example when a port is bound to a caller place that has the name of another declared place: a context operation that resolves the correspondence first resolves that place too, and no lookup order serves both styles there.

The correspondence is **single-valued**: each declared place resolves to exactly one actual place, while two declared places may resolve to one actual place when two ports are bound to one caller place ([MOD-020]) or two places are fused ([MOD-061]). It disambiguates branch selection that port-agnostic discovery cannot express cleanly: `ctx.output(declaredA)` on an `Out.xor(a, b)` transition produces exactly the actual `a` child, satisfying the exactly-one-production validator ([EXEC]). A **directly-composed** ([MOD-025]) or hand-written transition that no channel merge ([MOD-021]) has joined has the **identity** correspondence (an empty correspondence behaves exactly as today). The correspondence MUST remap correctly under **nested** instantiation ([MOD-013]): when an outer `instantiate(prefix)` renames an already-composed transition, the correspondence's **actual** side (its values) remaps through the same place remap applied to the arcs, while its **declared** side (its keys, the author-original places) stays fixed; so a declared place resolves through arbitrary nesting depth (e.g. `outer/inner/x`).

**Key-set completeness across passes.** The declared side staying fixed is a *completeness* requirement, not only a stability one: the correspondence's key set MUST remain the complete set of author-original places for that transition through every rewrite pass. In particular, an entry whose actual side happens to equal its declared place at some intermediate pass (by whichever equality that implementation's lookup uses — see below) — a place a binding rebound to a place of its own name, or one that a given pass left untouched — MUST NOT be discarded on that basis. The chained pass MUST NOT re-derive keys from the arcs, whose names are intermediate-pass names the author never declared; the correspondence is therefore the *only* carrier of the author-original key set, and a key dropped at an intermediate pass is unrecoverable. A later pass that renames such a place then has nothing to rewrite, and the action fails its declared-place check against a place that no longer exists in the composed net — after its inputs have already been consumed, so the tokens are lost ([EXEC-031]). An implementation MAY drop the correspondence **as a whole** when every entry is the identity, because a transition carrying no correspondence is rebuilt from its arcs on the next pass, and those names are still author-original.

**Which equality decides "identity".** Whether an entry is the identity MUST be decided by the **same** place equality that the correspondence's own lookup uses. An implementation whose correspondence is keyed by name alone treats `X → X` as the identity whatever the token types; one whose place equality is structural over name *and* token type ([MOD-024]) treats a mapping from `X` of one token type to `X` of another as a retained, non-identity entry — because its lookup would likewise tell them apart. Both are conforming, but tying the two together is not optional: an identity test **coarser** than the lookup discards entries the lookup would have resolved, reintroducing the loss this requirement forbids, and one **finer** than the lookup retains entries the lookup can never reach. This is the [MOD-024] divergence inherited, not a new one, and it applies equally to the merge rule below.

**Merging correspondences.** A composition form that merges two correspondences for a single transition (channel composition, [MOD-021]) MUST treat an identity entry as carrying **no assertion**. Where one side maps a declared place to itself and the other maps the same declared place to a different actual place, the **non-identity** mapping wins and the merge succeeds; only two differing **non-identity** mappings for one declared place are a genuine conflict and MUST be reported as one. This follows from key-set completeness: an identity entry records that some pass did not rename the place, not that the author required it to keep its name. Without this rule, retaining identity entries would manufacture merge conflicts that an implementation discarding them would never raise, making a correct correspondence *less* composable than a lossy one.

The correspondence belongs to the **action / binding layer**, not the structural net. It MUST NOT be consulted by enablement, firing, the verifier, the exporter, or the event subsystem. In particular it is not part of the structural-equivalence set enumerated by [MOD-023] AC#1 (place index, transition count, arc topology, bitmap masks, timing arrays) — it sits alongside [MOD-030]'s by-reference actions on the action side of that line. An implementation MAY realise the correspondence idiomatically: implementations whose actions invoke the context directly (e.g. an in-language `TransitionContext`) apply it inside the context API; a binding-hosted implementation MAY apply it in its binding adapter, in the same order (the correspondence first), and expose the correspondence to its native actions, whose context then does not resolve: a native action resolves a declared place through the exposed correspondence itself (Rust: `TransitionContext::local_name_map`). Both satisfy this requirement, and acceptance criteria 1, 2, 3 and 7 hold of such a native action when it resolves its declared places this way. The correspondence is purely structural (no runtime state) and is fixed for the lifetime of the composed net. This requirement is orthogonal to [MOD-030]: `bindActions` still swaps the action object; the correspondence is attached at the structural rewrite, independent of which action is bound. Binding or rebinding a transition's action ([CORE-042], [MOD-030]) MUST **preserve** this correspondence: the rebuild that swaps the action MUST carry it forward unchanged. Consequently an action MAY be bound *after* `instantiate` — the structure-only-subnet + late-binding idiom (`instantiate(prefix).bindActions(…)`, then `compose(bindPort(…))`) — and still resolve its declared place references under composition, exactly as a baked-in action does.

*When* a transition that carries no correspondence goes through a sequence of rewrite passes (instantiation, port binding, fusion) with no channel merge among them, the resulting correspondence *shall* resolve every place that the transition's arcs and output specification named before the passes to the place that the same sequence of place maps sends it to, which is the place that the same arc or output now names, and *shall* resolve every other place to itself.

*When* a rewrite pass rewrites a transition, the places that the transition's input, inhibitor, read and reset arcs and its output specification name, and in particular its input places and its output places, *shall* be the places they named before the pass, each sent through the pass's place map, so that place-set discovery returns the actual composed places.

A transition that carries no correspondence *shall* resolve every place to itself.

*If* the two correspondences that a channel merge joins for one transition resolve one place to two different places, neither of them that place itself, *then* the merge of the two correspondences *shall* fail.

*When* the two correspondences that a channel merge joins for one transition have no such conflict, the merge of the two correspondences *shall* succeed.

*When* a merge of two correspondences succeeds, the merged correspondence *shall* resolve each place to the place the caller side resolves it to when that differs from the place itself, and otherwise to the place the instance side resolves it to.

*When* an action is bound or rebound to a transition, before or after instantiation, the transition's correspondence, arcs and output specification *shall* stay unchanged.

*Where* an implementation resolves declared places in its context operations, *when* an action calls `inputs`, `input`, `inputToken`, `read` or the single or bulk `output` with a place, the call *shall* give the result, or report the error, that the same call gives on the same transition without a correspondence for the place that the transition's correspondence resolves the given place to.

**Runtime defect (RD-30):** the Python binding adapter tries the given name first: when that name is itself an input place of the transition for `input` and `inputs`, a read place for `read` or an output place for `output`, the call answers for that place and does not resolve it, so it breaks the rule above only on such a place that the correspondence resolves to another place, and there only when the two places give different results. The fix is to try the correspondence first, as the MAY paragraph above asks of a binding adapter.

**Acceptance Criteria:**
1. A subnet whose transition action does `ctx.input(declaredIn)` / `ctx.output(declaredOut, …)`, instanced and composed with `bindPort("in", req).bindPort("out", resp)`, fires and produces on the actual `resp` place with no "place not in declared inputs/outputs" error.
2. A transition with `Out.xor(aDecl, bDecl)` whose action selects `aDecl` produces exactly one token on the actual `a` place after instancing + port binding, and the exactly-one-production validator passes.
3. Under nested instantiation ([MOD-013]) — compose `T` into `S` (prefix `inner`), then instantiate `S` as `outer` — a hardcoded `T`-action's declared place resolves to `outer/inner/x` and the action fires.
4. A directly-composed ([MOD-025]) or hand-written transition that no channel merge ([MOD-021]) has joined carries the identity correspondence; its actions behave exactly as before this requirement (no observable change).
5. Place-set discovery is unchanged: `inputPlaces` / `outputPlaces` return the actual composed places; port-agnostic actions written against discovery continue to work on every discovered place that the correspondence resolves to itself.
6. Structural equivalence per [MOD-023] is preserved: a composed net and the equivalent hand-written flat net match on place index, transition count, arc topology, bitmap masks, and timing arrays — the correspondence is not part of that set.
7. An action bound *after* instantiation resolves its declared places exactly as a baked-in action does: a structure-only subnet (no baked action) instanced as `instantiate(prefix).bindActions({"t": action})` (or `bind_actions`), then composed with `bindPort`, fires and produces on the bound place with no "place not in declared inputs/outputs" error. The action-swap rebuild ([CORE-042]) does not drop the correspondence.
8. **Identity round-trip across passes.** This needs **three** passes, and a two-pass reading of it is satisfied by defective code — at two passes the identity-bound place's actual name still equals its declared name, so a lookup that tries the literal name first resolves it whatever the correspondence did. The third pass is what moves that place's actual name *away* from its declared name, and it comes from retrofitting the composed net as a subnet ([MOD-013]) and instantiating it again. So: a transition declaring two or more places, where one is bound at an intermediate pass to a place of its **own declared name** (an identity step) while another is renamed at that same pass, and a **later pass, over the retrofitted net,** renames both: the action resolves **both** declared places to their final composed places and fires. An implementation that discards the identity entry at the intermediate pass fails this — the transition enables, consumes its inputs, and only then fails its declared-place check, so the tokens are lost ([EXEC-031]) rather than the net failing to build.
9. An implementation that drops an all-identity correspondence wholesale still satisfies AC#8, because the next pass rebuilds the key set from the arcs.
10. **Identity never conflicts on merge.** Channel-composing ([MOD-021]) a transition whose caller-side correspondence maps `X → X` against an instance-side correspondence mapping `X → Y` succeeds and yields `X → Y`. Two differing non-identity mappings for `X` still raise a conflict.
11. **The identity test agrees with the lookup.** An entry the correspondence's lookup would resolve to a place *different* from its key is retained; one it would resolve to the key itself may be dropped. Under a name-and-token-type place equality ([MOD-024]) a mapping from `X` of one token type to `X` of another is therefore retained, and under a name-only equality it is the identity. An implementation satisfies this criterion by its own equality; it MUST NOT use one notion in the identity test and another in the lookup.

**Depends on:** [MOD-010], [MOD-013], [MOD-014], [MOD-020], [MOD-021], [MOD-023], [MOD-024], [MOD-025], [MOD-030], [MOD-061], [CORE-042], [EXEC-031]
**Test derivation:** Build a one-transition subnet whose action hardcodes its declared input/output places; instantiate with a prefix, compose binding both ports to caller places, run; assert it produces on the caller's output place with no declared-place error. Repeat with the instance nested inside an outer instance and assert resolution to the doubly-prefixed place. Assert a hand-written net with the same shape is byte-identical in its compiled structure. For AC#8, build a transition over a port place `x` and an internal place `y`; at the first pass bind the port to a caller place **also named `x`** while `y` is prefixed; retrofit the result as a subnet and instantiate it under a second prefix; run and assert the action resolves both `x` and `y` and produces — asserting on the executor run, not on the correspondence's shape, since the failure mode is consume-then-throw. A variant where *every* place round-trips to identity must also pass, covering AC#9.

---

## Export and Debug

#### MOD-040: Export Grouping (subgraph cluster_* per instance prefix)

**Priority:** SHOULD
**Kind:** F

DOT export per [EXP-001] of a composed net SHOULD emit a `subgraph cluster_<sanitizedKey>` block grouping the nodes of each subnet. The exporter determines a node's cluster key from one of two sources:

- **Subnet-membership metadata** ([MOD-026]), when the net carries any. A node mapped to subnet `S` is grouped under `cluster_<sanitize(S)>`; a node with no entry (a shared rendezvous place, or a node from instance composition) is not grouped by metadata.
- **Instance-prefix detection**, the fallback. A node whose name begins with `<prefix>/` is grouped under `cluster_<sanitize(prefix)>`; nested instance prefixes (per [MOD-013]) produce nested cluster subgraphs.

When the net carries membership metadata, the exporter SHOULD prefer it, and SHOULD fall back to instance-prefix detection for any node without a metadata entry, so a builder that mixes direct and instance composition keeps both cluster kinds. The cluster source MAY be made caller-selectable (e.g. an explicit metadata-only, prefix-only, or no-clustering override); the default SHOULD be the metadata-when-present behaviour above.

**The rule as an accessor.** Membership metadata answers "which subnet does this node belong to" only for direct composition, and the prefix answers it only for instance composition ([MOD-026] rule 4). The net SHOULD expose the combined answer as `subnetOf(name)`, which follows the default (`AUTO`) cluster rule above without its nesting, except that the prefix it falls back to is one some transition lives under:

1. `name` is not a place or transition of the net → absent;
2. else the membership entry for `name`, when there is one;
3. else the longest `/`-prefix of `name` that some transition of the net lives under: of the prefixes of `name` ending before one of its `/` characters, taken from longest to shortest (`a/b/c/x` gives `a/b/c`, then `a/b`, then `a`), the first non-empty `P` such that at least one transition of the net has a name beginning with `P/`;
4. else absent.

Step 3 walks up because a subnet may use `/` inside its own namespace: an instance `s1` whose body has a place `obs/TURN` contributes `s1/obs/TURN`, and the part before the last `/`, `s1/obs`, is no instance and carries no transition. Reading it as a subnet made encapsulation checks report a place of `s1` as belonging to a subnet of its own. For a transition name step 3 returns its own instance prefix (the transition itself begins with it), so transitions are attributed as by the part before the last `/`. The set of prefixes that head a transition SHOULD be computed once per net, lazily, so `subnetOf` costs O(depth of the name).

`subnetOf` therefore differs from the DOT `AUTO` cluster rule for a name with `/` inside a subnet's own namespace: the exporter still clusters `s1/obs/TURN` under `s1/obs`. The exporter's instance-prefix helper and its clustering are unchanged by this rule. `subnetOf` is additive: no export output, membership mapping or event changes.

For `subnetOf` and the instance-prefix helper, the SHOULD priority is whether an implementation offers them at all; an implementation that offers them answers as the next six sentences say.

In the four sentences on `subnetOf` that follow, a `/`-prefix of a name is a non-empty beginning of the name that is immediately followed by a `/`, and a `/`-prefix `P` heads a transition of the net when the name of some transition of the net begins with `P/`.

*If* `name` is neither a place nor a transition of the net, *then* `subnetOf(name)` *shall* be absent.

*When* `name` is a place or a transition of the net and the net's membership mapping ([MOD-026]) has an entry for `name`, `subnetOf(name)` *shall* return that entry.

*When* `name` is a place or a transition of the net with no membership entry and some `/`-prefix of `name` heads a transition of the net, `subnetOf(name)` *shall* return the longest such `/`-prefix.

*When* `name` is a place or a transition of the net with no membership entry and no `/`-prefix of `name` heads a transition of the net, `subnetOf(name)` *shall* be absent.

The instance-prefix helper (`instancePrefixOf`) *shall* return the part of a name before its last `/` when that part is not empty, and be absent otherwise.

The sanitization function applied to the key MUST match the existing DOT ID sanitization per [EXP-014] (non-`[A-Za-z0-9_]` characters, including `/`, replaced by `_`).

The cluster label SHOULD be the original (un-sanitized) key string (the prefix, or the subnet name) for human readability.

This requirement does NOT change the styling, junction, or arc-rendering rules of EXP-002..EXP-015; it only adds grouping structure.

For the export half of this requirement (the sentences on DOT export: the opening sentence and its two bullets, the preference and cluster-source sentences, the sanitization and label sentences and the sentence on EXP-002..EXP-015), the SHOULD priority is whether an exporter draws cluster subgraphs at all; an exporter that draws them reads every MAY, SHOULD and MUST sentence of the export half as *shall*, lets the caller select the metadata-only, prefix-only and no-clustering sources, uses the default source when the caller selects none, takes the cluster key of a node and the covered nets as [EXP-016] defines them, and follows the next three sentences, which restate shall sentences of [EXP-016].

The exporter *shall* make each node that has a cluster key a direct member of the cluster of that key and of no other cluster, make a node without a cluster key a member of no cluster, and list as a member of a cluster only a node it draws.

The exporter *shall* draw exactly one cluster for each cluster key of a drawn node and for each `/`-prefix of such a key and no other cluster, nest each cluster directly in the cluster whose key is the part of its own key before the last `/` and draw a cluster whose key has no `/` at the top level, and give the cluster of key K the ID `cluster_` followed by K sanitized per [EXP-014] and the label K.

The exporter *shall* draw, in any order, the same nodes, and the same edges other than the ghost edges of [EXP-017], as it draws for the same net and configuration under no clustering.

**Acceptance Criteria:**
1. Compose two instances with prefixes `b1` and `b2`; export DOT; verify the output contains `subgraph cluster_b1 { ... }` and `subgraph cluster_b2 { ... }` blocks.
2. Each cluster block contains, directly or through the cluster blocks nested in it, exactly the places and transitions whose cluster key is the cluster's key or begins with it followed by `/`, and the junction nodes of those transitions.
3. Nested instance prefixes produce nested cluster subgraphs.
4. A net with no composed instances and no membership metadata (no `/` in any name) produces no cluster subgraphs.
5. Cluster IDs match the regex `cluster_[A-Za-z0-9_]+` (sanitized per [EXP-014]).
6. A net carrying [MOD-026] membership metadata emits a `subgraph cluster_<subnetName>` block per subnet; each subnet's private nodes appear inside its block and a shared (multi-subnet) place whose name has no instance prefix appears at the top level.
7. With both membership metadata and `prefix/`-named instance nodes in one net, metadata-mapped nodes cluster by subnet name and prefix-named nodes cluster by prefix.
8. `subnetOf` on a directly composed node returns its subnet name; on an instance-composed node `b1/inner/p` of a net with a transition `b1/inner/t` it returns `b1/inner`; on a shared rendezvous place without `/`, a flat node without `/`, and a name the net does not declare, it is absent.
9. `subnetOf` walks up to a prefix some transition lives under: with a transition `s1/t`, the place `s1/obs/TURN` gives `s1`; a place `x/y` with no transition under `x/` is absent; with a nested transition `outer/inner/t`, the place `outer/inner/p` gives `outer/inner`; a membership entry wins over all of these. The DOT export of the same nets is byte-identical to before.

**Implementation notes:**
- Java: `PetriNet.subnetOf(String)` returns `Optional<String>`; the prefix helper is
  `org.libpetri.export.SubnetPrefixes.instancePrefixOf`.
- TypeScript: `PetriNet.subnetOf(name)` returns `string | undefined`; `instancePrefixOf` is
  exported from `libpetri/export`.
- Rust: `PetriNet::subnet_of(&self, name)` returns an `Option`; the prefix helper is
  `libpetri_core::subnet_prefixes::instance_prefix_of`, re-exported from
  `libpetri_export::subnet_prefixes`.
- Python: `Net.subnet_of(name) -> str | None`, and `Net.subnet_membership`, the [MOD-026]
  mapping as a `dict`.

**Depends on:** [MOD-010], [MOD-013], [MOD-026], [EXP-001], [EXP-014], [EXP-016]
**Test derivation:** Build a composed net with two top-level instances; export; assert cluster blocks present with correct membership and IDs. Build a directly-composed net of two subnets; export; assert one `subgraph cluster_<subnetName>` per subnet with the shared place, named without `/`, at top level.

---

#### MOD-041: Debug Protocol Subnet Instances

**Priority:** SHOULD
**Kind:** F

The debug protocol's `Subscribed` response (live net inspection) SHOULD carry, in addition to the existing place and transition descriptors, an enumeration of **subnet instance descriptors**. The descriptors are computed from the names of the flat net alone. The **instance prefix** of a node name is the part of the name before its last `/`; a name without `/`, or whose only `/` is its first character, has none. Each descriptor describes one distinct instance prefix that some place or transition name carries, which is usually one top-level or nested instance of the composed net, and includes:

1. The instance prefix string (e.g., `b1` or `outer/inner`).
2. The originating subnet definition's name, where available.
3. The parameter value supplied at instantiation, where available.
4. The set of transitions whose instance prefix is the descriptor's prefix (full prefixed names).
5. The set of places whose instance prefix is the descriptor's prefix (full prefixed names, reported as the exposed places). After composition these are the instance's own internal places (not those of instances nested in it) and its unbound ports: a bound port takes the name of the caller place it is bound to.
6. An optional parent-prefix field: the instance prefix of the descriptor's own prefix, which names the enclosing instance of a nested one.

Current runtimes keep neither the definition name nor the parameter value after composition, so items 2 and 3 are absent.

An outer instance all of whose nodes sit in a nested instance has no descriptor of its own; the nested descriptor names it as its parent. A subnet that uses `/` in its own names (the place `s1/obs/TURN` of [MOD-040]) also yields a descriptor, here `s1/obs`, that is no instance. A hand-written net with a `/` in a name gets descriptors too. A session over an imported archive carries no net topology; its subnet instance list is not specified here.

In addition, individual `PlaceInfo` and `TransitionInfo` entries in the debug protocol SHOULD carry an optional `instancePrefix` field derived from the name's prefix portion, so clients that do not parse names themselves can group nodes.

*When* a debug session subscribed to a live net answers `Subscribed`, its subnet instance list *shall* hold exactly one descriptor for each distinct instance prefix that the name of some place or transition of the net carries, and no other descriptor.

*When* a debug session subscribed to a live net answers `Subscribed`, each subnet instance descriptor *shall* list as its transitions exactly the transitions of the net whose instance prefix is the descriptor's prefix, and as its places exactly the places of the net whose instance prefix is the descriptor's prefix.

*When* a debug session subscribed to a live net answers `Subscribed`, each subnet instance descriptor *shall* carry as its parent prefix the instance prefix of its own prefix, and no parent prefix when its own prefix has none.

*When* a debug session subscribed to a live net answers `Subscribed`, the `instancePrefix` field of the `PlaceInfo` or `TransitionInfo` of every node *shall* be the instance prefix of the node's name, and *shall* be absent when the name has none.

This requirement is observability-only; it does not change net behavior.

**Acceptance Criteria:**
1. A debug session subscribed to a live composed net receives a list of subnet instance descriptors with one entry per distinct instance prefix that some place or transition name carries.
2. Each descriptor's transition and exposed-place sets enumerate exactly the transitions and places whose instance prefix is the descriptor's prefix.
3. Each `PlaceInfo` and `TransitionInfo` whose node name has an instance prefix carries that prefix as `instancePrefix`, and one whose name has none carries no `instancePrefix`.
4. Nested instances are reported with their parent prefix.
5. A debug session subscribed to a live net with no `/` in any name returns an empty subnet-instance list and no `instancePrefix` fields.

**Depends on:** [MOD-010], [MOD-013]
**Test derivation:** Subscribe to a debug session for a two-instance pipeline; assert the response carries two instance descriptors with the correct prefix, transitions, and exposed places.

---

## Verification

#### MOD-050: Verification Pass-Through on Composed Flat Net

**Priority:** MUST
**Kind:** B

All verification facilities specified in section 07 (VER) MUST operate on a composed flat net per [MOD-023] without any composition-aware adaptation. Specifically:

1. Property checks per [VER-002] (deadlock freedom, place bounds, mutual exclusion, unreachability).
2. P-invariant computation per [VER-005].
3. Structural analyses per [VER-020], [VER-021].
4. Untimed over-approximation per [VER-004].
5. State class graph analysis per [VER-010] where supported.

The verifier sees the composed net as a normal `PetriNet`. No modular extension to the verifier API is required by this requirement.

*When* a verification facility specified in section 07 (VER) runs on a net that `build()` returned, it *shall* give the result that section 07 specifies for the hand-written net with the same name, the same places in the same order, the same transitions in the same order with the same names, arcs, output specifications, timing, priorities and actions, and the same terminal places in the same order.

The result of a verification facility specified in section 07 (VER) *shall not* depend on which subnet a place or transition belongs to ([MOD-026]) or on the place correspondence of a transition ([MOD-031]).

**Acceptance Criteria:**
1. Run the SMT verifier on a composed pipeline net; verification completes and produces a result of the same shape as for a hand-written net.
2. Verification results on the composed net match results on the hand-written equivalent net (per [MOD-023]) that lists its places in the composed net's order. A result that does not depend on the order of places matches on every hand-written equivalent.
3. P-invariant computation succeeds and produces invariants over the composed (prefixed) place names.

**Depends on:** [MOD-023], [VER-001]
**Test derivation:** Verify deadlock-freedom on a composed producer/buffer/consumer pipeline; verify the same property on the hand-written equivalent; assert identical results.

---

#### MOD-051: SubnetDef.verify(harness) for local property verification

**Priority:** SHOULD
**Kind:** B

A subnet definition SHOULD support a local verification operation `verify(harness)` that proves properties of the subnet **in isolation**, without first composing it into an enclosing net. The harness supplies:

1. A `params` value of the subnet's parameter type.
2. For each input and in-out port, a token source. `verify` calls it once while it builds the synthetic net and discards the token, so a source that fails or returns no token makes `verify` fail. It does not bound the input: the environment mode of item 4 does.
3. The set of properties to check (per [VER-002]).
4. How injection into those environment places is modeled, per [VER-006]. It comes in the options of `verify` beside the harness, or the implementation defaults it.

The implementation realizes this by wrapping the subnet in a synthetic enclosing net where each input and in-out port is bound to an environment place and each output port to a place the properties can name, then invoking the standard verifier per [MOD-050].

Item 4, not the token sources of item 2, is what bounds the input (AC3). The synthetic net has environment places by construction, so the environment mode decides what a verdict is worth: under `Ignore` the verifier models no injection, and [VER-006] refuses to certify any `Proven` that results, so **a subnet with an input port can never be proven**. A `Violated` still comes back: for a reachability-safety property it is a counterexample with injection too, since a run without injection is a run with it, and for a quiescence property it is a rest of the subnet while the environment stays silent, which need not be a rest under injection ([VER-006]). `verify` therefore SHOULD default to `AlwaysAvailable`, under which a `Proven` holds for every environment, and SHOULD let the caller pass a mode instead. `Bounded(k)` caps the tokens **resident** in each input place at `k` and refills it forever ([VER-006]), so it bounds what one firing can take, not the input as a whole; `Arrivals(k)` is the mode that expresses a generator delivering at most `k` tokens to each input port over the whole run, and `Arrivals(min, max)` one delivering at least `min` of them; `Arrivals(k, k)` delivers exactly `k`, which a property counting outcomes against inputs at quiescence needs, since under `Arrivals(k)` a run that declines its arrivals always violates it.

**Verification options.** `verify` SHOULD accept an options value beside the harness, and the existing signatures keep working unchanged:

- the environment mode above;
- a **configure** hook, called once per property with the per-property verifier *after* the implementation's own setup (property, environment places, environment mode) and with the synthetic net, returning the verifier to run. It is how a caller sets anything the verifier offers: the per-call timeout and the total budget or cancellation of [VER-013], sink places, the state-equation and enumeration options, the ν options below. The synthetic net lets the hook resolve the names the harness's properties already use: the subnet's own places under the `sut/` prefix, the ports under their harness names. The hook has the semantics of the open-net `configureSmt` of [VER-022]: what it sets overrides the implementation's setup, and a hook that replaces the environment mode takes responsibility for it.

Python cannot hand a callback the Rust builder cheaply, so `verify_subnet` takes keyword arguments forwarded to each per-property verification instead: at least the keywords `verify` accepts for the timeout, total budget, cancellation, sink places, enumeration budget and state-space options, and the ν options (budget places, carrier places, fragment mode, the Route B class bound). Place names in them are the synthetic net's names, spelled as in the properties (`sut/<place>`). An unknown name behaves as it does in `verify`: an
unknown sink place is ignored, and an unknown carrier place makes the verdict `Unknown`.

**ν subnets need the ν options.** A subnet that mints and joins correlation names ([NU-010], [NU-020]) and threads a name through a relay is verified in the BASE fragment unless the caller says otherwise ([NU-051]). BASE reads such a relay as a fresh mint: a different model, in which a join the real net reaches may never fire, so a safety property can come back `Proven` although the net violates it. Declaring the carrier places and selecting the EXTENDED fragment through the options (the hook, or the Python keywords) is what makes the per-property verifier decide the subnet exactly; implementations SHOULD say so where they document `verify`.

**Binding actions on a definition.** A subnet definition SHOULD offer `bindActions(...)`, mirroring the net-level operation of [CORE-042] with the same argument forms (mapping and resolver) and, per form, the same treatment of transitions it does not name, divergence included. It is keyed by the definition's own, unprefixed transition names and returns a **new** definition whose ports, channels and parameters are unchanged; the receiver is not modified. Instances created from the new definition carry the bound actions as their shared defaults ([MOD-030]). The [CORE-043] check in `verify` applies to the bound definition as to any other.

*When* `verify` returns a result, the synthetic net it verified *shall* be the net that a new enclosing builder builds from one call that composes the subnet's instance under the prefix `sut`, binds each port to its harness place (`harness_in_<port>` for an input port, `harness_out_<port>` for an output port, `harness_io_<port>` for an in-out port), binds no channel and declares nothing else.

*If* instantiating the subnet under the prefix `sut` fails or building the synthetic net fails, *then* `verify` *shall* fail.

*If* the harness supplies no token source for an input or in-out port of the subnet, *then* `verify` *shall* fail and *shall* return no verification result.

*If* the harness supplies a token source for every input and in-out port and the [CORE-043] check fails on the synthetic net, *then* `verify` *shall* fail with an error that names the transition the check names, also when the harness lists no property.

*When* `verify` returns a result, the result *shall* hold an entry for each property of the harness and no entry for another property, and each entry for a property *shall* be the result of the standard verifier ([VER-003], [VER-006]) on the synthetic net, set up with that property, the harness places of the input and in-out ports as environment places, the selected environment mode, the verifier's default options and the empty initial marking, and then passed, together with the synthetic net, through the configure hook, whose changes override that setup.

*When* `verify` is called without options, it *shall* verify under the environment mode `AlwaysAvailable` with no configure hook.

*When* actions are bound on a subnet definition, in either form, the new definition *shall* have the name, the ports and the channels of the original definition and the place correspondence ([MOD-031]) of each of its transitions, in the same order.

*When* actions are bound on a subnet definition with a resolver or a mapping, the body of the new definition *shall* be the net that binding the same resolver or mapping on the original body gives at net level ([CORE-042]), so the resolver or the mapping is keyed by the definition's own, unprefixed transition names.

**Acceptance Criteria:**
1. Where provided, `verify(harness)` returns a verification result of the same shape as the standard verifier per [VER-003].
2. Invoking `verify` does not require the subnet to be composed into any enclosing net.
3. The environment mode of item 4, not the token sources, bounds the input behavior for the verification, and a missing token source for an input or in-out port is an error.
4. The environment-analysis mode of [VER-006] is selectable per verification and defaults to one that models injection, so a subnet with an input port is not refused a `Proven` by default.
5. `Arrivals(k)` is selectable, and bounds the total injected into each input port to `k`: a subnet that forwards each input token to an output port proves `placeBound` of that output at `k` under `Arrivals(k)` and violates it under `Bounded(k)`.
6. The configure hook (Python: the forwarded keywords) reaches every per-property verifier. A setting made there is visible in the result: a total budget too small to finish yields its exhaustion reason ([VER-013]), and a sink place named there changes a quiescence verdict.
7. **ν options reach the verifier.** A ν subnet whose property is `Proven` with the options unset (BASE) is `Violated`, or at least not `Proven`, once carrier places and the EXTENDED fragment are passed through the options: the options are shown to change the model, not merely to be accepted.
8. `bindActions` on a definition returns a new definition whose instances carry the bound actions, keyed by unprefixed names; the receiver's instances keep the old ones; ports and parameters are unchanged.

**Implementation notes:** TypeScript `verify(harness, options?: { environmentMode?, configure?: (verifier: SmtVerifier, synth: PetriNet) => SmtVerifier })`; Java `verify(harness, SubnetVerifyOptions)`, a record of the environment mode and a `BiFunction<SmtVerifier, PetriNet, SmtVerifier> configure`, with withers; Rust `SubnetVerifyOptions`, whose `configure` field takes the verifier and the synthetic net (`OpenNetOptions::configure_smt` plus the net); Python `verify_subnet(..., *, environment_mode=..., <forwarded keywords>)`. `bindActions` / `bind_actions` on `SubnetDef` in all four.

**Depends on:** [MOD-001], [MOD-030], [VER-001], [VER-006], [VER-013], [VER-022], [ENV-001], [CORE-042], [CORE-043], [NU-051]
**Test derivation:** Build a leaky-bucket subnet parameterised by rate; supply a harness with a request generator and leave its permit place unseeded; verify that the bucket's `accepted` place is `0`-bounded — unreachable however much the environment injects — under the default mode and under `Bounded(k)`, and that the same query is refused under `Ignore`. A forwarding subnet under `Arrivals(2)` against `Bounded(2)` (AC5); a total budget of 1 ms set through the hook (AC6); a fork → relay → join subnet with carrier places, verified with and without the ν options (AC7); `bindActions` on a definition, then two instances of the old and the new definition (AC8).

---

## Fusion (orthogonal to composition)

#### MOD-060: Fusion Set Declaration (orthogonal to composition)

**Priority:** MUST
**Kind:** F

A **fusion set** declares that N places — possibly drawn from different module instances — are to be treated as a single canonical place in the composed flat net. Fusion is **orthogonal to composition**:

1. Composition merges places via port-binding (one instance port place ↔ one caller place per binding).
2. Fusion merges N places at once via N-ary equivalence, after composition has flattened all subnet instances.

Fusion is the mechanism for modeling shared cross-instance state (e.g., a global rate limiter shared by three instances of a leaky-bucket subnet) without expressing the shared resource as an interface port on every subnet.

A fusion set has:
1. A name, used in diagnostics only. The first declared member is the canonical member, and it keeps its own name in the fused net ([MOD-061]).
2. A list of N member places in the order they were declared, N >= 1. A set with one member fuses nothing: its canonical member maps to itself.
3. All members MUST have compatible token types per [CORE-003] (implementation-defined enforcement matching [MOD-022]). Java and Rust compare the run-time token types of the members; TypeScript keeps no run-time token type and checks none. The Python binding declares no fusion sets.

*If* a fusion set is declared with no member, *then* declaring it *shall* fail.

*When* a fusion set is declared with at least one member and no two of its members have different run-time token types, declaring it *shall* succeed and *shall* return the set with its name and with its members in the order they were declared.

*Where* an implementation keeps a run-time token type for places (Java and Rust), *if* two members of a fusion set have different token types, *then* declaring the set *shall* fail.

**Order of operations relative to composition.** Port substitution per [MOD-020] and channel merging per [MOD-021] happen **first**, during each `compose(...)` call on the enclosing builder. Fusion sets are then applied to the resulting post-composition flat net during `build()` per [MOD-061]. Consequently, fusion membership is evaluated against **post-composition place identity**: a fusion set MAY validly name a caller-side place that became the destination of one or more port substitutions, and the resulting fused canonical place observes the unioned token bag of all arcs that, after composition, target the (now-substituted) caller place plus all arcs targeting other fusion members.

**Acceptance Criteria:**
1. A fusion set can be declared with a name and a list of N (>= 1) member places.
2. Fusion sets are independent of port bindings: the same caller place MAY be both a port-binding destination and a fusion member; applying fusion produces a flat net in which the canonical fused place is the substitution target for every arc that previously referenced any port-substituted instance place or any non-canonical fusion member.
3. Token-type incompatibility among members is rejected per [CORE-003], in the implementations that keep a run-time token type (Java and Rust).
4. Declaring a fusion set with no member is rejected as malformed; a fusion set with one member is accepted and fuses nothing.

**Depends on:** [CORE-003], [MOD-020]
**Test derivation:** Declare a fusion set with three members of type `Token<Permit>`; verify accepted. Declare with one member; verify it is accepted and the built net is unchanged. Declare with no member; verify rejection. Declare with mixed token types (Java and Rust); verify rejection. Compose an instance binding port `out -> P`, then declare a fusion set `{P, Q}`; build; verify the canonical fused place is the substitution target of every arc that previously referenced the renamed instance port place or `Q`.

---

#### MOD-061: Fusion Resolution at build()

**Priority:** MUST
**Kind:** F

When `build()` is invoked on an enclosing builder containing one or more fusion sets, the builder MUST:

1. For each fusion set, take its first declared member as the canonical member; the canonical member keeps its own name, and the name of the fusion set is used in diagnostics only.
2. Run a structural rewrite over every transition in the builder, substituting every non-canonical member with the canonical member in every input, output, inhibitor, read, and reset arc. When at least one input arc of a transition is on a member that is not the first declared member of its fusion set, all input arcs of that transition are reconciled after substitution by the canonical merge table of [MOD-021], with the same rejection cases and the same diagnostic shape; the seam is `Fusion set '<name>'`, where `<name>` is the name of the fusion set that lists the place of the pair, or the name of that place when no fusion set lists it. A transition with no such input arc is not merged, so duplicate input arcs it already had stay and the transition builder rejects them ([CORE-030]). Read, inhibitor and reset arcs that land on one place are kept as they are. Every rewritten transition passes through the transition builder again: the checks of [CORE-030], [IO-011], [IO-012] and [EXEC-012] apply to it, and a rewrite they reject fails `build()`.
3. Remove non-canonical members from the builder's place set; the canonical member remains. A terminal place ([EXEC-042]) declared on a non-canonical member names the canonical member in the built net.
4. Produce the resulting flat `PetriNet`.

Fusion MUST be applied **after** all `compose(...)` calls have flattened subnet instances into the builder. Fusion membership is checked against the **post-composition** place identity per [MOD-060]: a member may be any place that exists in the builder after all compositions, including caller places that became port-substitution destinations during `compose(...)`. The fusion rewrite MUST be applied before [CORE-040] returns the immutable net so that no downstream consumer sees the un-fused intermediate state. Removed members lose their subnet membership entry ([MOD-026]), and the retired-port check of [MOD-027] runs on the fused net.

**Ordering of multiple fusion sets: commutative when disjoint.** When the enclosing builder declares two or more fusion sets, `build()` applies them in an implementation-defined order. If the member sets of every pair of declared fusion sets are pairwise **disjoint** (no place is a member of more than one fusion set), the final flat net MUST be independent of that order: the result is observationally identical regardless of which fusion set is rewritten first. The order of application is internal to `build()`, so this is stated as independence from the order in which the fusion sets are declared; the order in which the built net lists its places is not part of it. Declaring two fusion sets that differ in name or in members and share a place MUST be rejected at build with a message naming a shared place and two fusion sets that list it, since the canonical choice and the order of application would otherwise alter the final structure. Declaring the same fusion set (same name, same members) twice is implementation-defined.

The result is a flat `PetriNet` per [MOD-023]; downstream consumers (executor, exporter, verifier, debug protocol) require no awareness of fusion.

The built net keeps no record of the fusion sets. An initial marking for a fused net names the canonical member: a token put on a non-canonical member stays on that name, which the built net does not declare, and is retained and inert per [CORE-072].

*When* fusion at `build()` succeeds on fusion sets of which no two share a member, the transitions of the result *shall* be the builder's transitions, in the same order and number, each with every member of a fusion set replaced by the first declared member of that set in every input, inhibitor, read and reset arc and in the output specification, with its name, timing, priority and action unchanged and, where at least one of its declared input arcs is on a member that is not the first declared member of its set, with its input arcs merged by the canonical merge table of [MOD-021] into one arc per place at the position of the first arc on that place.

*When* fusion at `build()` succeeds, every transition of the result *shall* pass the checks of the transition builder ([CORE-030], [IO-011], [IO-012], [EXEC-012]).

*When* fusion at `build()` succeeds on fusion sets of which no two share a member, the set of places of the result *shall* be the builder's places other than the members that are not the first declared member of their fusion set, together with the places a transition of the result names and the terminal places of the result.

*When* fusion at `build()` succeeds on fusion sets of which no two share a member, the set of terminal places ([EXEC-042]) of the result *shall* be the declared terminal places with every member of a fusion set replaced by the first declared member of that set.

*Where* no two declared fusion sets share a member, the outcome of fusion at `build()` *shall* be the same for every order in which the fusion sets are declared: the same failure with the same message, or a fused net with the same transitions in the same order, the same set of places and the same set of terminal places.

*When* no two declared fusion sets share a member and the rewrite of every transition meets no pair of input arcs that the canonical merge table of [MOD-021] does not list and passes the checks of the transition builder, fusion at `build()` *shall* succeed.

*If* no two declared fusion sets share a member and merging the input arcs of a rewritten transition meets two arcs on one place whose pair the canonical merge table of [MOD-021] does not list, *then* fusion at `build()` *shall* fail.

*If* no two declared fusion sets share a member and the transition builder rejects the rewrite of a transition, *then* fusion at `build()` *shall* fail.

*If* two declared fusion sets that differ in name or in members share a member, *then* fusion at `build()` *shall* fail with the message `Fusion overlap: place '<p>' appears in two fusion sets ('<first>' and '<second>'). A place may appear in at most one fusion set (MOD-060).`, where `<p>` is a member that two declared fusion sets both list and `<first>` and `<second>` are the names of those two sets, the one declared first named first.

*If* exactly two fusion sets that differ in name or in members are declared and they share exactly one member `p`, *then* the message of that failure *shall* name `p`, then the set declared first, then the set declared second.

*If* every transition before a transition `t` rewrites and passes the checks of the transition builder, no two declared fusion sets share a member, and the first off-table pair met while merging the input arcs of `t` lies on a member of a fusion set, *then* fusion at `build()` *shall* fail with the [MOD-021] rule (c) diagnostic for that pair, whose earlier side is the merge of the arcs before it on that place, whose seam is `Fusion set '<name>'` with the name of that set, and whose method spelling is one of the two that [MOD-021] allows.

*If* every transition before a transition `t` rewrites and passes the checks of the transition builder, no two declared fusion sets share a member, and the first off-table pair met while merging the input arcs of `t` lies on a place that no fusion set lists, *then* fusion at `build()` *shall* fail with the same diagnostic, the name of that place standing in the seam for the name of a set.

**Acceptance Criteria:**
1. Three instances of a leaky-bucket subnet share a global rate-limiter via a single fusion set over their three internal limiter places. The built net contains one canonical limiter place; arcs that originally referenced any of the three members now reference the canonical.
2. Tokens put on a non-canonical member at initial-marking time stay on that undeclared name, retained and inert per [CORE-072]; tokens meant for the fused place are put on the canonical member.
3. Non-canonical member places do NOT appear in the built net's place set.
4. Fusion is applied after composition: composing then fusing is observationally equivalent to writing a single hand-written net with the fused topology directly. Input arcs colliding on the canonical place follow the [MOD-021] merge table; off-table pairings are rejected at build with the diagnostic naming the fusion set.
5. Re-exporting and re-verifying the fused net works without any awareness of fusion in the consumer.
6. Multiple fusion sets with **disjoint** member sets are commutative: building the same enclosing builder twice, with its fusion sets declared in opposite orders, MUST produce flat nets that are observationally identical (identical place set, transition set, arc topology, executor behavior), or the same rejection with the same message.
7. Declaring two fusion sets that differ in name or in members and share at least one place MUST be rejected at build with a message naming a shared place and two fusion sets that list it.

**Depends on:** [MOD-021], [MOD-023], [MOD-060], [CORE-040]
**Test derivation:** Build three leaky-bucket instances composed into one builder, with their limiter places joined as a fusion set. Build the net; assert (a) only one canonical limiter place exists in the place set, (b) every transition originally referencing any of the three limiter members now references the canonical, (c) executor behavior matches a hand-written equivalent. Declare two disjoint fusion sets; assert order-independence of the built result. Declare two overlapping fusion sets; assert build is rejected. Fuse two places each consumed via `one()` by the same transition; verify the built net consumes 2 from the canonical place. Fuse places whose colliding input arcs cannot merge; verify build rejection names the fusion set. Declare `b` terminal and fuse `{a, b}`; verify `a` is terminal in the built net.
