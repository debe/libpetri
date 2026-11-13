import Libpetri.Spec.Text

requirement_text MOD_027
  id "MOD-027"
  title "References to Bound Ports"
  priority MUST
  kind B
  body r#"Instance composition ([MOD-020], and [MOD-024]'s auto-bound form) replaces a bound port's
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

⟦s1|*If* no composition of the builder binds one renamed place to two different caller places and a transition of the builder after fusion, one added to the builder or one a composition added, names a retired place in an arc of any kind or in its output specification, *then* `build()` *shall* fail, whatever the order in which the transition and the composition that retired the place were added.⟧

⟦s2|*If* a transition that fusion rewrites without an input-arc collision, that passes the transition builder's checks before and after fusion, and that after fusion consumes from or reads no terminal place and names exactly one retired place, is added to a builder whose net builds and whose fusion sets share no place, before or after its other calls but after every auto-bound and direct composition ([MOD-024], [MOD-025]), and no composition of the builder binds one renamed place to two different caller places, *then* `build()` *shall* fail with the message `place '<place>' is port '<port>' of instance '<instance>', bound to host place '<caller>' at compose; reference '<caller>' instead`, where `<place>` is that retired place and `<port>`, `<instance>` and `<caller>` are the port, the instance prefix and the caller place of a binding by which the first composition that retired the place retired it.⟧

⟦s3|*When* a transition that fusion rewrites without an input-arc collision, that passes the transition builder's checks before and after fusion, and that after fusion names no retired place and consumes from or reads no terminal place, is added to a builder whose net builds and whose fusion sets share no place, before or after its other calls but after every auto-bound and direct composition, and no composition of the builder binds one renamed place to two different caller places, `build()` *shall* still succeed.⟧

⟦s4|*When* one more place, a retired place included, is declared on a builder whose net builds, before or after its other calls but after every auto-bound and direct composition, and no composition of the builder binds one renamed place to two different caller places, `build()` *shall* still succeed.⟧

⟦s5|*When* a `compose(instance, bindings)` call without channel bindings takes the place of a direct composition ([MOD-025]) of the instance's transitions rewritten through its bindings on a builder whose net builds, with no auto-bound or direct composition after it, and the call binds every port at most once, only ports the instance declares, each port to a caller place of its port's token type ([MOD-022]) and one renamed place to one caller place only, no other composition of the builder binds one renamed place to two different caller places, the instance's transitions have distinct names and no input or output collision under the bindings ([MOD-020]), and no transition of that net names a place the call retires, `build()` *shall* still succeed.⟧

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
`A_IN`; the build succeeds."#
