import Libpetri.Spec.Text

requirement_text MOD_024
  id "MOD-024"
  title "Identity-Default Port Inference (auto-compose)"
  priority SHOULD
  kind B
  body r#"The enclosing net's builder SHOULD support a single-argument `compose(instance)` overload that auto-binds every interface port declared on the subnet to the host place carried on that port's declaration. For each `port` returned by `instance.def().iface().ports()` the implementation MUST contribute a binding `(port.name() → port.place())`; the resulting binding map MUST be processed identically to an explicit `compose(instance, map)` call per [MOD-020]. The result MUST therefore satisfy [MOD-023] (composition produces a flat net) with no observable difference from the explicit form.

When the subnet declares no interface ports, the implementation MAY additionally infer bindings by walking the instance's renamed body and matching each renamed place against the host builder's place set, probed by the place's original (un-prefixed) identity. Body places that do not match stay private under their prefixed names per [MOD-010] and [MOD-012]. The probe identity SHOULD use the implementation's existing `Place` equality (per [CORE-002]); implementations whose `Place` equality is name-only MAY still implement the body-inference path but MUST document the more permissive matching contract in their API surface.

Channels are NOT auto-bound. If the subnet's interface declares any channel, `compose(instance)` MUST raise an error naming the channels and directing the caller to the explicit-binding `compose(instance, bindings)` overload per [MOD-021]. Transition identity is too delicate for inference. Caller code is expected to think about which caller-side transition fuses with which channel.

The single-argument form is **additive** sugar over [MOD-020]; it does NOT replace the explicit-binding overloads. Callers SHOULD use the Consumer/Map overloads when (a) they need to rewire a port to a host place other than the one the SubnetDef declared, (b) the subnet has any channel, or (c) the subnet defines reusable ports whose host targets differ across instances.

⟦s1|*When* `compose(instance)` is called on an instance whose subnet declares at least one port and no channel, the builder *shall* give the same result as `compose(instance, bindings)` with each declared port bound to the place on that port's declaration, the same rejection included.⟧

⟦s2|*If* the subnet of an instance passed to `compose(instance)` declares a channel, *then* `compose(instance)` *shall* fail with an error that names every channel the subnet declares.⟧

⟦s3|*Where* the builder infers bindings for a subnet without ports, *when* `compose(instance)` succeeds on an instance whose subnet declares no port and no channel and whose transitions have pairwise distinct names, the builder *shall* keep its transitions and add the instance's transitions in order, each with every arc and output place on a renamed body place `p/x` moved to `x` when the builder held `x` at the call, by the implementation's `Place` equality, every other place kept, its name, timing, priority and action unchanged and its declared-to-actual place correspondence ([MOD-031]) moved the same way or, when every entry of it then maps a place to itself, dropped as a whole as [MOD-031] allows, *shall* add to its places exactly the places those transitions name, and *shall* leave its terminal places, retired ports, subnet membership and fusion sets as they were.⟧

⟦s4|*Where* the builder infers bindings for a subnet without ports, *when* `compose(instance)` is called on an instance whose subnet declares no port and no channel and whose transitions have pairwise distinct names, `compose(instance)` *shall* succeed exactly when every instance transition, with each renamed body place `p/x` moved to `x` when the builder holds `x`, passes the transition builder's checks.⟧

**Acceptance Criteria:**
1. `compose(instance)` over a subnet with port `out: Output<T>` carrying host place `P` produces a net structurally equal to `compose(instance, map{out: P})`.
2. When the host builder did not pre-declare `P`, `P` MUST arrive in the merged net via the rewritten port arcs (same flow as explicit `bindPort`).
3. When the subnet declares no interface ports, body places equal to host places (by the implementation's `Place` equality per [CORE-002]) merge; other body places remain prefix-renamed.
4. `compose(instance)` on a subnet that declares any channel raises an error naming the channels and suggesting the explicit-binding overload.
5. Auto-compose followed by `build()` is observationally indistinguishable from the explicit `compose(instance, bindings)` followed by `build()` for the same target wiring (places, transitions, arcs, timing, priority, actions all equal).
6. An empty subnet (no body places, no transitions, no ports, no channels) composes as a no-op: the host builder's place/transition sets are unchanged.

**Depends on:** [MOD-003], [MOD-005], [MOD-010], [MOD-020], [MOD-023]
**Test derivation:** Build a subnet with port `out` carrying host place `P`; compose via `compose(instance)` and via `compose(instance, b -> b.bindPort("out", P))`; assert the resulting flat nets are structurally identical (place set, transition names in order, per-transition arc topology). Compose a subnet that declares a channel; verify the call is rejected with a message naming the channel and pointing at the explicit overload. Compose two instances of a producer-style subnet through a shared host place; verify both producer transitions emit to the same host place."#
