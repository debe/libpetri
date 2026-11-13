import Libpetri.Spec.Text

requirement_text NU_040
  id "NU-040"
  title "Bounded Budget and Decidability"
  priority SHOULD
  kind F
  body r#"Be explicit about the cliff. **Safety / coverability** for the ν-fragment is
**decidable** [RV-08]: the marking-with-names state space is a well-structured transition
system. Full **reachability / liveness** with *unbounded* fresh names and
*unbounded* recirculation is **undecidable** in general (ν-PN reachability is
undecidable [RV-11]).

A **bounded budget** is the decidability lever, not merely operational hygiene.
Model it structurally: a typed `Budget` place pre-seeded with `k` tokens whose
single token a fork consumes when it mints a name and a join (or a dead-letter
transition) returns. Then:

- "at most `k` live correlation groups" is the structural invariant
  `PlaceBound(Budget, k)` ([VER-002]); once the budget place is declared to the verifier,
  it is checkable with the existing untimed encoder, no name reasoning required;
- a `Pending` place (one token per live group, emptied only by join or
  dead-letter; a correlation group is live from the fork that mints its name until a join
  or dead-letter takes its `Pending` token) plus `PlaceBound(Pending, k)` and quiescence
  ([VER-002]) to `Pending = 0` expresses **"every forked name is joined or dead-lettered
  by the time the net comes to rest."**

With the budget bounded and branch places `PlaceBound`-checked, fresh names are
drawn from a finite live pool, the WSTS stays finite, and these properties become
provable. This is the [reask/retry-budget-as-typed-place] discipline applied to
correlation.

Declaring a budget place to the verifier also declares the mint contract of [NU-010]
for every transition that has an input arc on it: where such a transition writes a coloured
place without consuming one, the ν routes read the write as a fresh name.

⟦s1|*Where* a place is declared to the verifier as a budget place, the ν routes *shall* read every transition that has an input arc on that place as a declared mint ([NU-010]).⟧

⟦s2|The ν routes *shall* read a transition named as a mint transition on the verifier (`mintTransitions` / `mint_transitions`) as a declared mint, whatever budget places are declared.⟧

⟦s3|The ν routes *shall* read a transition as a declared mint only when it is named as a mint transition on the verifier or has an input arc on a place declared to the verifier as a budget place.⟧

A read, inhibitor or reset arc on a budget place declares nothing.

**JoinedOrDeadLettered.** The property `JoinedOrDeadLettered(pending)` says that no correlation
group is left behind when the net comes to rest: no reachable quiescent marking holds a
`pending` token. A run that never comes to rest does not violate it.

⟦s4|Every route that decides `JoinedOrDeadLettered(pending)` *shall* count a marking as violating it when the marking is quiescent ([VER-002]) and `pending` holds a token, whether or not a declared sink place is marked.⟧

⟦s5|Every route that decides `JoinedOrDeadLettered(pending)` *shall* count a marking as violating it only when the marking is quiescent and `pending` holds a token.⟧

⟦s6|In that quiescence a transition with a match specification *shall* count as enabled exactly when it is enabled as [NU-020] says: on its token counts, and with a name of which every correlated input holds at least one token and at least its required count; a match that correlates no input is never enabled.⟧

A route that reads enablement on token counts alone does not decide `JoinedOrDeadLettered(pending)`
on a net with a transition that has a match specification, and answers `Unknown` there ([NU-050]).

**Acceptance Criteria:**
1. A fork gated on a `Budget` input cannot mint more than `k` concurrently-live
   names; `PlaceBound(Budget, k)` holds.
2. A net whose every forked name is joined or dead-lettered reaches `Pending = 0`
   at quiescence; `PlaceBound(Pending, k)` holds.
3. The spec states plainly that without a bounded budget, reachability/liveness
   over unbounded fresh names is undecidable, and that the verifier answers that case
   as [NU-050] AC2 says: never `Proven`.
4. `JoinedOrDeadLettered(pending)` is exactly "no reachable quiescent marking holds
   a `pending` token", quiescent as in [VER-002], with a transition that has a match
   specification enabled as in [NU-020]. It carries **no sink clause**: declared sink places
   ([VER-002]) do not weaken it, and a stranded correlation group is a violation
   whether or not some sink happens to be marked in the same marking. Every route
   that decides it decides this same predicate.

**Depends on:** [VER-002], [EXEC-040], [NU-010], [NU-020]
**Test derivation:** Build a scatter-gather net with a `Budget(k)` place, declare the
budget place to the verifier, and verify `PlaceBound(Budget, k)` and `PlaceBound(Pending, k)`
with the untimed encoder."#
