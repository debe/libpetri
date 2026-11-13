import Libpetri.Spec.Text

requirement_text MOD_025
  id "MOD-025"
  title "Direct Composition (compose a subnet without instantiation)"
  priority MUST
  kind B
  body r#"The enclosing net's builder MUST support a direct-composition operation that
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

⟦s1|*When* direct composition of a subnet definition into an enclosing builder succeeds, the builder *shall* hold its earlier transitions followed by the body's transitions in the body's order, each unchanged and under its original name, and its earlier places together with every body place and every place a body transition names, a body place equal to a place it already holds being that place, no place added twice, and nothing else of the builder changed but the subnet membership of [MOD-026].⟧

⟦s2|*If* a body transition's name is the name of a transition already in the enclosing builder, *then* direct composition *shall* fail at the call.⟧

⟦s3|*If* the subnet definition declares no terminal place and no channel and exactly one name of its body transitions is the name of a transition already in the enclosing builder, *then* the error *shall* name that transition and the subnet definition.⟧

⟦s4|*If* the interface of a subnet definition declares a channel, *then* direct composition of that definition *shall* fail at the call.⟧

⟦s5|*Where* place identity carries the token type ([CORE-002]), *if* a body place has the name of a place the enclosing builder holds and a different token type, *then* direct composition *shall* fail at the call.⟧

⟦s6|*When* a subnet definition that declares no terminal place ([EXEC-042]) and no channel is composed directly into an enclosing builder that holds no transition with the name of a body transition and, where place identity carries the token type, no place with the name of a body place and a different token type, direct composition *shall* succeed.⟧

⟦s7|*If* two subnet definitions that declare no terminal place, and whose body transitions name only their own body places, are composed directly one after the other into one builder and both calls succeed, *then* composing them in the other order *shall* also succeed in both calls and give a builder with the same places and the same transitions, each with its arcs, timing, priority and action.⟧

⟦s8|*If* the body of a subnet definition declares a terminal place ([EXEC-042]), *then* direct composition of that definition *shall* fail at the call.⟧

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
Direct-compose a channel-declaring subnet; assert rejection naming the channel."#
