# Composition reference

Reusing net structure: subnets, ports, channels, instances, fusion. Spec: `spec/11-modular-composition.md` (MOD-001..MOD-061) inside a libpetri checkout, otherwise
https://github.com/debe/libpetri/blob/main/spec/11-modular-composition.md.

## Contents

1. [The model: open nets, glued ports, flat result](#1-the-model-open-nets-glued-ports-flat-result)
2. [Ports and channels](#2-ports-and-channels)
3. [Instantiate, compose, direct compose, fuse](#3-instantiate-compose-direct-compose-fuse)
4. [Channel merge algebra](#4-channel-merge-algebra)
5. [Designing a subnet worth reusing](#5-designing-a-subnet-worth-reusing)
6. [Worked example: one leaky bucket, used twice](#6-worked-example-one-leaky-bucket-used-twice)
7. [Actions and binding](#7-actions-and-binding)
8. [Place equality diverges across languages](#8-place-equality-diverges-across-languages)
9. [What breaks composition](#9-what-breaks-composition)

---

## 1. The model: open nets, glued ports, flat result

Composition is **build-time only**. A `SubnetDef` is an open net (a body plus an interface). You instantiate it under a prefix, glue its interface places onto caller places, and the builder rewrites arcs. After `build()`, the runtime, exporter, verifier and event system all see a normal flat `PetriNet` (MOD-023). Nothing downstream is composition-aware, and the compiled result is identical to a hand-written equivalent (MOD-050).

This is the open-net model from the Petri net literature, not hierarchical refinement. Say instantiate, compose, glue ports, fuse places. Do not say refine, expand a transition, or child net: there is no runtime hierarchy to expand, and the vocabulary sends people looking for a nesting mechanism that does not exist. Cluster boxes in an exported diagram are a drawing convenience reconstructed from name prefixes; the net underneath is flat.

Open nets are type-distinct from closed nets and cannot be executed (MOD-002). Interfaces are validated at build time, not later (MOD-006).

## 2. Ports and channels

- **Port** = interface *place*. Synchronizes at the place level: the subnet's port place becomes the caller's place. This is how data crosses the boundary.
- **Channel** = interface *transition*. Synchronizes at the transition level: the caller's transition and the subnet's transition merge into one transition that fires as one atomic step, with arcs unioned.

Reach for a channel only when two sides genuinely must fire together as one step. Ports cover almost everything, and they compose without the merge algebra's sharp edges.

**Port direction is advisory metadata only** (MOD-004). Arcs govern flow. An `Output` port may be consumed internally; an `Input` port may be read internally. Never encode a constraint in direction: nothing enforces it, and a reader who trusts it will be wrong.

A place can be both an interface port (a composition boundary) and an environment place (a world boundary). They are orthogonal concepts. Environment registration applies to the post-composition identity.

## 3. Instantiate, compose, direct compose, fuse

**`instantiate(prefix, params)`** renames every place and transition to `prefix + "/" + originalName` (MOD-010). Per-instance state isolation is a pure consequence of that renaming (MOD-012): distinct names give distinct place identities, distinct token bags, independent timing clocks. There is no runtime isolation mechanism, and none is needed. Nested prefixes concatenate associatively.

`/` is the reserved separator. Never put it in a place name, transition name or subnet name: it drives prefix parsing and cluster reconstruction in export, and must be sanitized out of membership metadata (MOD-010, MOD-026).

**`compose(instance, bindings)`** substitutes the instance's renamed port place with the caller place at every arc, brings internal places in under their prefixed names, and adds every transition (MOD-020). Eager, at compose time. Binding a port twice in one call is a build error.

**`compose(instance)`** with no bindings auto-binds each port to the host place carried on its declaration (MOD-024). Channels are never auto-bound: a subnet declaring a channel must use the explicit form.

**Direct composition** (MOD-025) composes a definition with **no** prefixing. Places merge by name equality, order-independently; transition name collisions are rejected. Use it for a single shared copy of something. If you need two independent copies, you must go through instantiate plus compose: direct composition merges them into one.

**Fusion** (MOD-060, MOD-061) merges N places into a canonical member at `build()`, after all composition, against post-composition identity. This is how you model state shared across instances (one global rate limiter seen by three instances) without threading a place through every subnet's interface. A fusion set needs at least two members, and two fusion sets may not share a place.

## 4. Channel merge algebra

Merging two transitions unions their arcs, and this is where the sharp edges live.

**Timing merges by interval intersection**, in a merge algebra where `Immediate` counts as `[0, 0]` (not the firing interval `[0, inf)` it has at run time): `Deadline(d) = [0, d]`, `Delayed(d) = [d, inf)`, `Window(e, l) = [e, l]`, `Exact(d) = [d, d]`. An empty intersection is rejected naming both timings. The trap: merging an `Immediate` channel with a `Delayed(d>0)` caller is rejected, because `[0,0]` and `[d,inf)` do not overlap.

**Priority: the caller side wins** by default.

**Actions compose sequentially**, caller side first, exposed as one atomic firing of one transition, invoked once per fire.

**Input arcs on the same place merge by a fixed table** (MOD-021, also normative for fusion): `one + one -> exactly(2)`; `one + exactly(n) -> exactly(n+1)`; `exactly(n) + exactly(m) -> exactly(n+m)`; `all + all -> all`; `atLeast(n) + atLeast(m) -> atLeast(max(n,m))`. Everything else is rejected. `Read`, `Inhibitor` and `Reset` have no cardinality dimension and collapse. **Different arc types on the same place are always rejected.**

## 5. Designing a subnet worth reusing

- **One responsibility, stated as its ports.** If you cannot name the subnet's input and output ports in a sentence, it is not a component yet.
- **Keep it structure-only and bind actions per instance** (MOD-030). A `SubnetDef` that carries no actions can be instantiated many times in one process with different behaviour bound to each copy. Actions carry through by reference; `bindActions` is last-wins replacement, not chaining, and never mutates the receiver.
- **Name places for the domain, not for the caller.** A subnet whose port is called `ORDER_FROM_CHECKOUT` cannot be reused by anything but checkout. `REQUEST` and `RESULT` can.
- **Do not duplicate place-name strings across the subnet and its orchestrator.** Export the port constants from the subnet and have the caller reference them. A typo in a duplicated name silently creates a second, unconnected place, and the net will simply never fire that transition. That failure looks like a logic bug and is one of the most expensive mistakes in this model.
- **Watch static-initialization cycles.** If a subnet class holds static place constants and the orchestrator holds static subnet definitions that reference each other, class-initialization order can hand you nulls at build time. Keep the definition side free of back-references to the orchestrator.
- **Prefer many small instances over one shared place set.** Isolation by renaming costs nothing at run time and is dramatically cheaper to verify: fewer interleavings, disjoint name pools.
- **Verify the subnet in isolation as you write it** (MOD-051). It wraps each input port in an environment place, so the environment mode decides everything: under `Ignore` a subnet with an input port can never be proven. Default to `AlwaysAvailable`, or `Bounded(k)` when the caller really supplies at most k.

## 6. Worked example: one leaky bucket, used twice

A rate limiter is the best first subnet to build, because it is small, every service needs one, and
it is the case where "the limit lives in the marking" pays off immediately. Here is the whole thing.

### The subnet

```
SubnetDef "leakyBucket", params (burst: int, interval: Duration)

  ports:   REQUEST   (in)      typed, carries the call
           ADMITTED  (out)     the call, cleared to proceed
           THROTTLED (out)     the call, refused
  body:    PERMITS             unit tokens, seeded with `burst`
           TICK                one unit token, the refill clock

  Admit:   In.one(REQUEST), In.one(PERMITS)               -> ADMITTED
  Refuse:  In.one(REQUEST), inhibitor(PERMITS)            -> THROTTLED
  Refill:  In.one(TICK), delayed(interval),
           inhibitor-guarded so PERMITS stops at `burst`  -> and(TICK, PERMITS)
```

Three things to notice, because they are the reusable ideas rather than the specific net:

- **`Admit` and `Refuse` consume the same `REQUEST` token.** Exactly one of them fires, decided by
  whether a permit exists at that instant. There is no window between "check the limit" and "make
  the call", because the check *is* the consumption.
- **The clock is a token.** `TICK` circulates through `Refill`, and the delay restarts each time it
  lands. No scheduler, no background thread, nothing outside the net to reason about.
- **The cap is structural.** `Refill` is blocked when `PERMITS` is already at `burst`, so
  `PlaceBound(PERMITS, burst)` is provable, and with the in-flight place included you get the
  conservation law `admitted_in_flight + PERMITS = burst` for free.

Keep the definition structure-only. Bind the action that actually performs the call per instance.

### Occasion one: two independent limiters

The triage net calls a CRM and a knowledge base. Different vendors, different quotas, no shared
budget. Instantiate the same definition twice under different prefixes with different parameters:

```
crmLimiter = leakyBucket.instantiate("crm", { burst: 5,  interval: 1s })
kbLimiter  = leakyBucket.instantiate("kb",  { burst: 20, interval: 1s })

net.compose(crmLimiter, bind(REQUEST -> CRM_CALL_REQUESTED,
                             ADMITTED -> CRM_CALL_READY,
                             THROTTLED -> CRM_CALL_DEFERRED))
   .compose(kbLimiter,  bind(REQUEST -> KB_CALL_REQUESTED,
                             ADMITTED -> KB_CALL_READY,
                             THROTTLED -> KB_CALL_DEFERRED))
```

Prefixing gives `crm/PERMITS` and `kb/PERMITS` as genuinely separate places with separate token
bags and separate refill clocks. That isolation is a consequence of the renaming, not a runtime
feature, and it costs nothing. The two limiters cannot interfere even in principle, which is also
why the verifier finds this cheap: the interleavings do not multiply the way they would if both
shared one place.

### Occasion two: the same limiter, shared

Now the quota is per account, not per vendor: both call paths draw from one bucket of 10 calls a
second. Do **not** reach for direct composition to "share" the subnet, and do not thread a permit
place through every caller's interface. Instantiate as before and fuse the permit places at build:

```
net.compose(crmLimiter, ...)
   .compose(kbLimiter, ...)
   .fuse("crm/PERMITS", "kb/PERMITS")
   .fuse("crm/TICK",    "kb/TICK")
   .build()
```

Fusion merges the named places into one canonical place after all composition, against
post-composition identity. The two `Admit` transitions now compete for the same permits, which is
exactly the shared quota, and it is expressed as topology rather than as a shared limiter object
that both call sites hold a reference to. Seed the fused place once, with the shared burst.

One caution specific to this shape: fusing the `TICK` places means one refill clock rather than two,
which is what you want for a shared quota, and fusing only `PERMITS` while leaving two ticks would
refill the shared bucket at twice the intended rate. Fuse the clock with the bucket, or keep both
separate. This is the kind of mistake a diagram catches instantly and a code review does not.

### What it buys you at proof time

With either arrangement, `PlaceBound` on the permit place is provable, the conservation law is
linear and survives the exact gate (there is no draining arc and no reset arc anywhere in the
subnet, which is not an accident), and "a call can always eventually proceed or be refused" is a
deadlock-freedom question the verifier can answer. A limiter built as an object with a counter
supports none of those statements.

## 7. Actions and binding

Actions may hardcode the places they declared (MOD-031). A declared-to-actual correspondence is established at compose time and applied inside the context's `input` / `inputs` / `read` / `output` lookups before the declared-set check, remapping through arbitrary nesting depth and surviving a re-bind. So `instantiate(prefix).bindActions(...)` followed by `compose(bindPort(...))` works: the action keeps referring to its own subnet-local place and reaches the composed one.

Discovery methods (`inputPlaces` / `outputPlaces`) still return the *actual* composed places, which is what you want for generic code.

Two `bindActions` calls naming the same transition leave exactly one action bound, the last. If you want both behaviours, compose them yourself in one action.

## 8. Place equality diverges across languages

Auto-inference and direct composition use the implementation's own `Place` equality, and the three engines differ:

| | Place identity | Same name, different type |
|---|---|---|
| Java | `record (name, tokenType)`, structural on both | do **not** merge; the type conflict is rejected naming both types |
| TypeScript | `interface { name }` plus a phantom type parameter | merge silently; `tsc` is the only enforcement |
| Rust (and Python) | name-only `PartialEq`/`Hash`, `PhantomData` does not participate | merge silently |

**Design rule: never rely on the token type to keep two places apart.** Make names unique. A portable design has to be more conservative than any single implementation, and Java's stricter behaviour is the one that will not travel.

## 9. What breaks composition

- Binding the same port twice in one call, or the same caller transition to two channels in one call.
- Disjoint channel timings (the `Immediate` plus `Delayed` case above).
- Input-arc cardinality combinations outside the merge table.
- Different arc types on the same place.
- Transition name collisions in direct composition.
- Reaching for direct composition when you needed per-instance state. The symptom is two "instances" sharing one token bag.
- A fusion set with fewer than two members, or two fusion sets sharing a place.
- `/` anywhere in a name.
- A nu match spec silently dropped at a channel merge. It must fuse coherently or be rejected (NU-060).
