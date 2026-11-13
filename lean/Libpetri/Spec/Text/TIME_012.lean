import Libpetri.Spec.Text

requirement_text TIME_012
  id "TIME-012"
  title "Clock Restart on Intermediate Disablement"
  priority MUST
  kind T
  body r#"A firing of transition `t` has two halves: its inputs are consumed and its reset places drained, then its outputs are deposited. ⟦s1|The marking between the halves is the intermediate marking `M - Pre(t)` of Berthomieu and Diaz.⟧ Any other transition that was armed before `t` fired and is not enabled in the intermediate marking loses its clock, and is newly armed when it is enabled again afterwards, so its clock restarts from zero ([TIME-011]). ⟦s2|This holds even when `t`'s own outputs refill the place, and it holds whether `t`'s action completes synchronously or asynchronously: a synchronous action MUST NOT hide the gap.⟧ ⟦s3|The intermediate marking comes from the live marking `t` fires from: the tokens in the places when `t` fires, minus what `t` consumes.⟧ ⟦s4|Inside a firing pass this includes tokens a synchronous action deposited earlier in the same pass, because they are really there and a transition they keep enabled was never disabled.⟧ ⟦s5|Outputs of an asynchronous action still in flight are not in the marking yet, so they do not count.⟧ This differs from the enablement recheck of the pass ([EXEC-003] AC3-AC5), which does not count a same-pass deposit: that rule decides which transitions may still fire in the pass, this one decides which clocks survive a firing. ⟦s6|A transition that the recheck finds disabled ([EXEC-003] AC3) is disarmed and loses its clock as well, even when a same-pass deposit refilled its place and keeps it enabled in the live marking.⟧ ⟦s7|It is newly armed, with a fresh stamp, by a later enablement update that finds it enabled ([TIME-010]).⟧

⟦s8|*When* a transition `t` fires, each armed transition other than `t` that is not enabled in the intermediate marking *shall* lose its clock.⟧

⟦s9|*When* a transition `t` fires, each armed transition other than `t` that is enabled in the intermediate marking and after the firing *shall* keep its stamp.⟧

⟦s10|*When* a transition fires, it *shall* lose its clock.⟧

⟦s11|*When* a transition `t` fires and a transition that lost its clock in that firing is enabled after it, that transition *shall* be newly armed ([TIME-010]).⟧

⟦s12|A matched transition ([NU-020]) is armed only while it is enabled and some name is eligible ([NU-022]), in the intermediate marking as in any other marking.⟧

⟦s13|*When* a transition `t` fires, each armed matched transition other than `t` that is not enabled in the intermediate marking or has no eligible name there *shall* lose its clock, even when its correlated inputs still hold tokens.⟧

⟦s14|*When* a transition `t` fires and a matched transition that lost its clock in that firing has no eligible name after it, that transition *shall not* be newly armed, even when it is enabled after the firing.⟧

⟦s15|*When* a transition `t` fires, each armed matched transition other than `t` that is enabled with an eligible name both in the intermediate marking and after the firing *shall* keep its stamp, even when `t` took tokens of the name it would have joined on.⟧

⟦s16|*If* the enablement recheck of a firing pass finds a transition disabled ([EXEC-003] AC3), *then* the transition *shall* lose its clock, even when a same-pass deposit keeps it enabled in the live marking.⟧

⟦s17|*When* a firing pass starts a transition `t`, each other armed transition that is not enabled in the intermediate marking of `t` *shall* lose its clock at the next enablement update ([EXEC-001] step 3), even when a deposit before that update refills its places, and that update *shall* stamp it with the reading the update takes if it is enabled ([TIME-010]), after which its clock runs from that stamp.⟧

⟦s18|Until that update the transition keeps its old stamp, so it can still start later in the same pass on that stamp if the recheck finds it enabled; this needs an inhibitor arc, because without one a transition that is not enabled in the intermediate marking of `t` is not enabled in the pass-visible marking at a later start either.⟧

- ⟦s19|Removing tokens disables a transition only through input arcs, read arcs, cardinality requirements and ν-join bindings, never through inhibitor arcs.⟧
- ⟦s20|A reset arc drains its place, so every armed transition with a read arc on a reset place, or an input arc on it whose required count is positive, starts a fresh clock when it is enabled again, unless a same-pass deposit that the reset does not take ([EXEC-003] AC5) keeps it enabled in the intermediate marking.⟧
- Surplus tokens keep the clock. If `P` holds two tokens, `t` takes one and `t'` needs one, `t'` stays enabled in the intermediate marking and its clock continues.
- ⟦s21|The fired transition itself always starts a fresh clock when it is enabled again.⟧

The state class graph applies the same rule to persistence ([VER-010]). A transition that stays marked enabled across the firing announces its fresh clock with `TransitionClockRestarted` ([EVT-005]). If the executor observed it disabled in between, for example while an asynchronous action was in flight, its re-enablement emits `TransitionEnabled` instead ([EVT-004]).

**Acceptance Criteria:**
1. T consumes from place P and is enabled. Another transition consumes P's token and deposits a token into P in one firing, with a synchronous action. T's clock restarts: with `delayed(d)`, T fires no earlier than `d` after the refill.
2. As AC1, but T only reads P. T's clock restarts.
3. As AC1, but the other transition drains P through a reset arc and deposits a new token. T's clock restarts.
4. As AC1, but P holds two tokens and the other transition takes one and returns it. T's clock continues, and neither `TransitionClockRestarted` nor `TransitionEnabled` is emitted for T after the refresh.
5. AC1 with an asynchronous action restarts T's clock as well.
6. Each restart emits exactly one of `TransitionClockRestarted` or `TransitionEnabled`.
7. A join J correlates places P0 and P1 by name ([NU-020]). P0 holds a token of name 1 and then one of name 2, P1 a token of name 1, and J is armed. Another transition takes P0's head (name 1) and puts a token of name 1 back into P0 in one firing. J's clock restarts, although both inputs held tokens throughout.
8. As AC7, but P0 and P1 each hold a token of name 1 and then one of name 2, and the other transition takes P0's head (name 1) and puts nothing back into P0. J's clock continues, because name 2 stays eligible, and neither `TransitionClockRestarted` nor `TransitionEnabled` is emitted for J.
9. Two joins share P0: J1 correlates P0 and P1, J2 correlates P0 and P3. P0 holds a token of name 1 and then two of name 2, P1 two tokens of name 2, P3 a token of name 1, and both joins are armed. J1 fires on name 2. J2's clock continues, because name 1 stays eligible, and J1 starts a fresh clock.

**Depends on:** [TIME-010], [TIME-011], [CORE-034], [EXEC-003], [EXEC-013], [EVT-004], [NU-020], [NU-022]
**Test derivation:** A timer place P feeds a delayed transition T. An injected activity token fires a refresh transition that takes P's token and puts one back: through an input arc, with T only reading P, through a reset arc, and with a surplus token in P. Repeat the input-arc case with an asynchronous action. Assert a lower bound on T's firing time and the fresh-clock event, or its absence in the surplus case. For the ν-join clause, a join J correlates two inputs by name: a refresh takes the head of one input and returns a token of the same name (AC7), a taker removes one shared name while another stays shared (AC8), and a second join sharing an input fires on another name (AC9). Assert J's restart, or its absence, and the fired join's fresh clock."#
