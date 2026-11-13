import Libpetri.Spec.Text

requirement_text VER_020
  id "VER-020"
  title "Siphon and Trap Analysis"
  priority MAY
  kind F
  body r#"The engine may support structural analysis of siphons (sets of places that, once empty, stay empty) and traps (sets of places that, once marked, stay marked).

**Commoner's theorem governs ORDINARY nets only.** The siphon and trap fixpoints are computed
from the pre/post vectors, so they model a net in which the sole reason a transition is disabled
is an input place holding too few tokens. A read arc, an inhibitor arc, a reset arc, a
consume-all input or an input arc weight above one is a disablement the fixpoints do not see,
and dropping it yields a strictly **more permissive** net, the wrong direction for a deadlock
proof. An implementation that converts a siphon/trap result into a `Proven` verdict MUST
therefore refuse to do so for any net carrying one of them, exactly as it already refuses when
sinks are declared or environment places are registered on the net it decides. Three
witnesses, each a net that is dead at its initial marking and was reported deadlock-free before
the restriction: `t1: one(a) read(g) → g` with `t2: one(g) → a` from `{a:1}`;
`t: exactly(2, a) → a` from `{a:1}`; `t: one(a) inhibitor(b) → a` from `{a:1, b:1}`.

**Commoner's theorem needs at least one transition.** On a net with no transition every marking
is dead, yet each marked place is a siphon whose maximal trap, the place itself, is marked, so
the condition holds vacuously. An implementation MUST NOT convert the structural result into a
`Proven` for such a net. Witness: one place `a`, no transition, from `{a:1}`; it is quiescent at
once with a token stranded, a `DeadlockFree` violation.

**A structural proof needs every minimal siphon, each with an initially marked trap.**
Commoner's condition quantifies over all siphons; checking the minimal ones suffices, because a
trap inside a minimal siphon lies inside every siphon that contains it. An implementation MUST
therefore find **every** minimal siphon before it concludes "no potential deadlock", and MUST
require each one's maximal trap to hold a token in the **initial** marking; an empty or unmarked
trap is a potential deadlock. Growing a siphon by committing to one input of each producer (the
first, or all of them) is incomplete: it can miss exactly the empty siphon that makes the net
dead. Deciding the condition is co-NP-complete, so the search MAY run under a budget; past it
the result is inconclusive, never a proof. Two witnesses, each dead at its initial marking with
a token stranded: `t1: one(g) one(x) → y, g` with `t2: one(h) one(y) → x, h` from
`{g:1, h:1}` (minimal siphon `{x, y}`); `t1: one(a) one(c) → b, c` with `t2: one(b) → a` from
`{c:1}` (minimal siphon `{a, b}`).

⟦s1|*When* the siphon search returns, every set it returns *shall* be a nonempty siphon that contains no other nonempty siphon.⟧

⟦s2|*When* the siphon search returns, every nonempty siphon *shall* contain a set it returns.⟧

⟦s3|The maximal trap the check computes inside a set of places *shall* be a trap inside that set that contains every trap inside it.⟧

⟦s4|*If* the net has more than 50 places or no transition, *then* the structural check *shall* answer inconclusive.⟧

⟦s5|The structural check *shall* pass the siphon search a budget of 10 000 search nodes.⟧

⟦s6|*If* the siphon search does not return, *then* the structural check *shall* answer inconclusive.⟧

⟦s7|*When* the siphon search returns on a net with at most 50 places and at least one transition, the structural check *shall* answer no potential deadlock exactly when the maximal trap inside each returned siphon holds a token in the initial marking, and potential deadlock otherwise.⟧

⟦s8|*While* the total budget of [VER-013] is not spent, the siphon search *shall* return at a budget of 10 000 search nodes on the two witnesses above with minimal siphons `{x, y}` and `{a, b}`.⟧

⟦s9|*If* the total budget of [VER-013] is spent before the siphon search starts on a net with at least one place, *then* the siphon search *shall not* return.⟧

**A match transition hides a dead marking from the flat net.** A match transition ([NU-020])
joins tokens by identity, which the flat net does not see: the flat net enables the join
whenever the counts are there, so it can have no dead marking while the net it stands for has
one. The structural route therefore does not decide a net with match transitions, as it does
not decide one with a reapable transition ([VER-002]) unless `assumeNoReaping` is set.

⟦s10|The verifier *shall* convert a no-potential-deadlock answer into a `Proven` only when it decides `DeadlockFree` on a net with no match transition ([NU-020]), no reapable transition ([VER-002]) unless `assumeNoReaping` is set, no read, inhibitor or reset arc, no consume-all input, no input arc weight above one, no declared sink or conditional sink and no environment place registered on the net it decides (the `Arrivals` rewrite of [VER-006] leaves none).⟧

**Acceptance Criteria:**
1. Siphons and traps are identified from the net structure.
2. Results inform deadlock analysis (every siphon containing an initially marked trap ensures
   deadlock-freedom of an ordinary net; liveness only for free-choice nets).
3. A structural `Proven` is offered only for `DeadlockFree` on a net with no match transition,
   no reapable transition (unless `assumeNoReaping` is set), no read, inhibitor or reset arc, no
   consume-all input, no input arc weight above one, no declared sink or conditional sink and no
   environment place registered on the net the verifier decides (the `Arrivals` rewrite of
   [VER-006] leaves none). Each of the three witnesses above returns a verdict from a route that
   models what disables them, never a structural proof. Nor is a net with no transition: the
   one-place witness above is `Violated`, not proven structurally.
4. The siphon search is complete: it finds `{x, y}` and `{a, b}` in the two witnesses above, and
   neither net is proven structurally. A siphon whose maximal trap is empty in the initial
   marking (the ring `a ↔ b` from the empty marking) blocks a structural proof. A net with more
   than 50 places or an exhausted search budget yields an inconclusive result.

**Test derivation:** Net with known siphon/trap structure; verify identification."#
