import Libpetri.Spec.Text

requirement_text NU_052
  id "NU-052"
  title "Conflict-Only Priority for the Route B Name-SCG"
  priority MAY
  kind F
  body r#"The [VER-012] name-aware state-class graph (Route B) is otherwise priority- and
timing-blind: it expands every base-enabled transition, a sound over-approximation
of the executor's schedule. On the timed dead-letter-drain idiom — an immediate,
higher-priority matched consumer (a ν-join) competing for a coloured token with a
delayed, lower-priority orphan drain — that blindness reports a **spurious stall**:
the graph explores the drain stealing a live, about-to-be-matched token and
stranding its co-mint sibling, an interleaving the eager, priority-ordered executor
never produces.

An implementation MAY offer an opt-in **conflict-only priority** mode
(`prioritySemantics` / `priority_semantics`) that prunes exactly those unreachable
firings. Under `CONFLICT`, a base-enabled transition `L` is not expanded from a
class when another enabled transition `H` in the same class

- has strictly higher priority (`H.priority() > L.priority()`),
- shares at least one **consumed** input place with `L` **under real competition** —
  some shared consumed place `p` whose token count in the class marking cannot
  satisfy both demands at once (`count(p) < demand_H(p) + demand_L(p)`, where each
  demand is the sum of the required counts ([IO-007]) of that transition's input arcs
  on `p`: 1 for `One` and `All`, `n` for `Exactly(n)` and `AtLeast(n)`). Read and
  inhibitor arcs do not count, and a place holding **enough tokens for both** (e.g.
  two independent coloured tokens) is *not* a conflict — pruning `L` there would be
  unsound,
- becomes **ready no later than `L`** by the class-relative *residual earliest*: the
  DBM lower bound of each enabled clock captured **before** time is let to pass
  (`readyEarliest`, parallel to the enabled set). `H` pre-empts `L` only when
  `readyEarliest[H] <= readyEarliest[L]` (within a float epsilon). This is the exact
  DBM-relative test — a static `H.earliest() <= L.earliest()` does **not** suffice,
  because the class-relative enabling epochs can leave `H`'s clock behind `L`'s — and
  it **subsumes** the immediate-`H` case (`readyEarliest[H] == 0 <= readyEarliest[L]`)
  while additionally pruning sound non-zero-earliest conflicts (e.g. a delayed `H`
  that still becomes ready before a later-delayed `L`). And
- **actually fires** in this class — a name-disabled join, whose inputs carry no
  shared name, produces no name-successor and MUST NOT pre-empt a conflicting drain.

⟦s1|*While* the mode is `CONFLICT`, the Route B graph *shall* leave a base-enabled transition `L`
unexpanded from a class exactly when another transition `H` of the net pre-empts `L` in that
class, and *shall* expand every other base-enabled transition of the class as under `NONE`, in
the same order.⟧

⟦s2|*While* the mode is `CONFLICT`, the Route B graph *shall* take two transitions `H` and `L` to
compete in a class exactly when some place is a consumed input of both and its token count in
the class marking is less than the sum of their demands on it, where a transition's demand on a
place is the sum of the required counts ([IO-007]) of its input arcs on that place.⟧

*While* the mode is `CONFLICT`, the Route B graph *shall* take `H` to be ready no later than `L`
in a class exactly when `readyEarliest[H] <= readyEarliest[L]` within a float epsilon, where
`readyEarliest` is the DBM lower bound of each enabled clock before time is let to pass.

The default mode, `NONE`, MUST reproduce the prior Route B behaviour byte-for-byte.

⟦s3|*While* the mode is `NONE`, the Route B graph *shall* expand each base-enabled transition of a
class, in the class's clock order (the code-point order of the transitions' names, [VER-010]
AC1), with the successors the transition has when it is expanded alone from the same class and
the same base layer, *shall* expand no other transition, and *shall not* read the readiness,
in-flight state or competition of any transition.⟧

⟦s4|*While* the mode is `NONE`, the Route B graph *shall* give a base-enabled transition at least one
successor labelled with its name when the base layer can fire one of its branches in the class
and the transition will fire on the name layer (always for an ordinary or minting transition,
with an enabling name for a join, with a resident name for a consumer).⟧

**Soundness.** The pruning removes only interleavings in which a lower-priority
transition fires ahead of a ready, conflicting, strictly-higher-priority one —
behaviour libpetri's eager, priority-ordered executor never produces. `L` is not
lost: in any class reachable after `H` fires, `L` is re-examined and expands once
the conflict is gone. Two side-conditions keep the mode sound and precise: the
*residual-earliest* comparison (`readyEarliest[H] <= readyEarliest[L]`) prunes iff
`H` is genuinely ready no later than `L` in the class DBM, and the *multiplicity*
precondition prunes only when the shared consumed place cannot satisfy both demands
at once — a place holding a token for each transition is no conflict. The
name-disabled-join side-condition (`willFire`) rounds this out on ν-nets: a join
that cannot consume the contested token must not suppress a genuine straggler.

**In-flight actions.** The argument above reads each firing as one step. The executor
deposits a firing's outputs only when its action completes ([VER-004], [CONC-002]), and
two cases break the pruning. A transition `t` that feeds `H`'s input with an action in
flight leaves `H` disabled, so the executor fires `L` first while the one-step model
enables `H` at once and prunes `L`. And `H` itself in flight is not started again by the
Java and TypeScript executors, so a refill of the contested place goes to `L`. So a
verifier MUST, whenever conflict priority applies to a call (below), split every pruner
`H` (a transition with strictly higher priority than another it shares a consumed input
with) and every transition that deposits into an input or read place of a pruner, except a
transition that models an environment or is a completion step ([VER-004]), and MUST NOT
let `H` pre-empt anything while `inflight:<H>` is marked. When one of those transitions
cannot be split (a ν-join, or a writer into a coloured place, [VER-004]), the pruning is
off for that call: the verdict is the `NONE` verdict and the report names the transition,
unless the split without the pruning is refused as well, when the call answers `Unknown`
with that refusal. The idiom above is such a case, because the join is a pruner and cannot be
split. Under `assumeAtomicFiring` nothing is split and the pruning stays on, and the report
states the atomic assumption. A direct call to Route B (Rust `verify_via_name_scg`,
TypeScript `verifyViaNameScg`) applies no split and prunes as before; the in-flight guard
has no effect on a net without in-flight places.

Conflict priority does not apply to a call on a net with a transition read as reapable
([VER-002]); under `assumeNoReaping` none is. A late executor reaps a reapable pruner and then
fires the transition it would have pre-empted, so no firing can be pruned for it.

⟦s5|*While* the mode is `NONE`, conflict priority *shall not* apply to any call, and the verifier
*shall* hand the in-flight split ([VER-004]) the `QuiescentCount` demand alone.⟧

⟦s6|*While* the mode is `CONFLICT`, conflict priority *shall* apply to a call exactly when no
transition of the net is read as reapable ([VER-002]) and either the property is a
name-alignment one ([NU-055]) or the net has a ν-join and the property is not a
reachability-safety one with a declared budget place ([NU-050]), and the verifier *shall*
verify every other call as under `NONE`.⟧

⟦s7|*While* conflict priority applies to a call and `assumeAtomicFiring` is set, the verifier
*shall* keep conflict priority on.⟧

⟦s8|*While* conflict priority applies to a call and `assumeAtomicFiring` is not set, *if* the net
has no pruner or every transition the verifier would split under conflict priority can be
split, *then* the verifier *shall* split every pruner and every transition that deposits into
an input or read place of a pruner, except a transition that models an environment or is a
completion step ([VER-004]), and *shall* keep conflict priority on.⟧

⟦s9|*While* conflict priority applies to a call and `assumeAtomicFiring` is not set, *if* the net
has a pruner and a transition the verifier would split under conflict priority cannot be split,
*then* the verifier *shall* hand the in-flight split and Route B what it hands them under
`NONE`, so the verdict is the `NONE` verdict, and *shall* name the first such transition, in the
transition order, in the report, unless the split under `NONE` is refused too, when the call
answers `Unknown` with that refusal ([VER-004]).⟧

⟦s10|*While* the mode is `CONFLICT`, the Route B graph *shall* take a transition `H` to have a firing
in flight in a class exactly when the class marking holds a token on the place `inflight:<H>`.⟧

**Acceptance criteria (MAY):**
1. `NONE` is the default and the only mode an implementation MUST provide; when
   `CONFLICT` is offered, `NONE` MUST leave every existing Route B verdict unchanged.
2. The fork-threaded co-mint plus immediate ν-join plus delayed lower-priority drain
   fixture is `Violated` under `NONE` (the spurious stall) and `Proven` deadlock-free
   under `CONFLICT` (the join always wins the contested token) on Route B called
   directly, and through `verify()` under `assumeAtomicFiring`. Through `verify()` with
   the split on, the join cannot be split, so the verdict equals the `NONE` verdict and
   the report says conflict priority is off.
3. `CONFLICT` MUST NOT over-prune: a genuine orphan — a coloured token with no
   matching sibling, so the join is name-disabled — still reports `Violated` when no
   drain clears it and `Proven` when a drain does.
4. Only consumed-input conflicts prune; a read or inhibitor arc on the shared place
   creates no conflict.
5. The residual-earliest rule prunes non-immediate conflicts: a **delayed** ν-join
   (e.g. `delayed(100)`) still pre-empts a **later-delayed** lower-priority drain
   (e.g. `delayed(200)`) they conflict on, so `DEADLETTER` is unreachable under
   `CONFLICT` though reachable under `NONE`.
6. The multiplicity precondition prevents over-pruning: when the shared consumed
   place holds enough tokens for both transitions (e.g. two independent coloured
   tokens), `CONFLICT` MUST NOT prune the lower-priority transition.
7. A pruner in flight pre-empts nothing: with `H: one(c) → ok` at priority 10 and an
   asynchronous action, `L: one(c) → bad` at priority 0, `g: one(s) + inhibitor(c) → c`,
   and a declared ν pair beside them, from `{c, s}`, `Unreachable(bad)` under `CONFLICT`
   is `Violated` with `L` in the trace. The Java and TypeScript executors mark `bad`.

**Depends on:** [VER-012], [NU-050], [NU-020], [VER-004], [VER-002], [VER-010], [IO-007],
[NU-055], [CONC-002], [EXEC-002], [EXEC-003]
**Test derivation:** the minimal ν-join vs. timed dead-letter-drain fixture is
`Violated` under `NONE` and `Proven` under `CONFLICT`; a genuine orphan is `Violated`
under `CONFLICT` without a drain and `Proven` with one; every verdict is attributed
to Route B."#
