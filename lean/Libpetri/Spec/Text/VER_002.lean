import Libpetri.Spec.Text

requirement_text VER_002
  id "VER-002"
  title "Safety Properties"
  priority SHOULD
  kind F
  body r#"**Quiescence.** Every property below that speaks of a quiescent marking reads it
**reap-aware**. A transition is *reapable* when its timing is `Deadline` or `Window`: an
executor that is late past its latest bound plus the tolerance reaps it ([TIME-013]), leaves
its input tokens where they are, and does not arm it again until a firing or an injected token
writes one of its arc places. A late executor can therefore come to rest at a marking that still enables a
reapable transition (Lean `ReapingVsUntimed.reaping_refutes_ver004_ac3`). ⟦s1|A marking is
**quiescent** when every transition whose enablement check passes on it is reapable.⟧ On a net without a reapable
transition this is the plain reading, no transition enabled, and every script, verdict and
report is what it was before reaping was accounted for. ⟦s2|"All transitions disabled" in the
error conditions below means "every transition that is not reapable is disabled".⟧

Every route reads this one quiescence (AC7). The encoders leave a reapable
transition out of the quiescence clause of `Bad`, on the fixpoint query, the certificate
check, the [VER-018], [VER-019] and [VER-025] phases and Route A alike. A graph route treats an expanded
class as resting when every transition it enables is reapable (the ν name-partition graph of
[VER-012]: when every firing out of it is of a reapable transition).

Route B keeps timing ([NU-050]). A late executor also fires late: it reaps a `Deadline` or
`Window` transition, and it fires an `Exact` one after its bound, since [TIME-006] enforces
`Exact` softly. A graph under strong semantics forbids both, so it can prove a marking property
that a late executor violates (Lean `TimedScg/Retrodict.reaping_escapes_timed_graph`: `t1: p → a`
at `deadline(5)` and `t2: p → b` at `delayed(10)` never mark `b` on time, and a late executor
marks it). Route B therefore builds its graph, for **every** property, with the latest bound of
every `Deadline`, `Window` and `Exact` transition dropped and the earliest kept: `deadline(d)` is
read as `immediate()`, `window(e, l)` as `delayed(e)` and `exact(a)` as `delayed(a)` (Lean
`TimedScg/Late.relax`, sound by `late_run_sound`). It does not prune by priority ([NU-052]) on a
net with a reapable transition. A net timed only with `Immediate` and `Delayed` has no latest
bound to drop, and its graph, verdict and report do not change. The structural route of [VER-020] rules
out dead markings only, so it does not decide a net with a reapable transition. The open-net
routes of [VER-022] read the same quiescence.

An implementation MUST offer an opt-out, `assumeNoReaping` (`assume_no_reaping`), that
assumes an **on-time executor**: no transition is reaped and none fires after its latest
bound. It restores the plain quiescence and Route B's strong-semantics graph. The report of a
verdict reached under it on a net with a reapable transition, or on a ν-net with a `Deadline`,
`Window` or `Exact` transition, MUST say that the verdict assumes no transition is reaped and
an on-time executor, and the report of a quiescence verdict read reap-aware on a net with a
reapable transition MUST name the reapable transitions. When Route B drops a latest bound its
report MUST name the transitions whose bound it dropped. ⟦s3|The marking properties (`PlaceBound`, `Unreachable`, `MutualExclusion`) do not
read quiescence, and their scripts do not depend on the option.⟧

The following safety properties can be verified:

- **DeadlockFree**: no reachable quiescent marking exists where a token is stranded.
  Optionally, the verifier accepts **sink places**: expected terminal
  places where coming to rest is permitted. ⟦s4|Without a conditional sink declaration
  ([VER-014]), the error condition is: (all transitions disabled) ∧ (some marked place is
  not a declared sink).⟧ A quiescent marking violates
  exactly when it leaves a token outside the declared terminals — workflow-net proper
  completion. With no sinks declared this degenerates to: any quiescent marking still
  holding a token.
- **TerminatesAtSink**: every reachable quiescent marking has at least one declared sink
  marked. ⟦s5|The error condition is: (all transitions disabled) ∧ (no sink place has a token).⟧
  This asks the weaker question "did the net come to rest at a declared terminal at all",
  and says nothing about tokens left elsewhere. It is meaningful only when at least one
  sink is declared; with none, every quiescent marking violates vacuously.
- **MutualExclusion(p1, p2)**: places p1 and p2 never both have tokens simultaneously.
  ⟦s6|Over a list of places the property is **pairwise**: violated iff some two entries of the
  list, at different positions, hold a token at once, which is the conjunction of
  `MutualExclusion(pi, pj)` over every pair.⟧ Every route and encoder of an implementation
  that accepts a list MUST read it this way (a disjunction of pairwise conjunctions, not "all
  marked" and not "at most one token in total"); a list of two is exactly
  `MutualExclusion(p1, p2)`, whose SMT term stays `(and (>= m_p1 1) (>= m_p2 1))`. ⟦s7|A place
  listed twice pairs with itself, so `MutualExclusion(p, p)` is violated by any token in `p`;
  a list of fewer than two entries is never violated.⟧ An implementation MAY accept exactly two
  places (Java and TypeScript do; Rust and Python take a list). A linear route
  ([VER-015]) proves a list of three or more pair by pair.
- ⟦s8|**PlaceBound(place, k)**: place never has more than k tokens⟧
- ⟦s9|**Unreachable(places)**: the given set of places is never all simultaneously non-empty.⟧
  ⟦s10|The set is assumed non-empty: the property is not specified over an empty one.⟧
- **QuiescentCount(places, min, max, waivedBy)**: every reachable quiescent marking holds
  between `min` and `max` tokens across `places`; the lower bound is waived while any
  `waivedBy` place holds a token, the upper bound never. ⟦s11|The error condition is: (all
  transitions disabled) ∧ ((Σ < min ∧ every `waivedBy` place empty) ∨ Σ > max).⟧ With a
  designed-terminal marker ([VER-014]) as waiver, a halted run need not refund its budget but
  never holds more than there is. ⟦s12|A place listed twice in `places` is counted once.⟧

  `max` MAY be unbounded, represented however the implementation chooses (the representation
  is not observable). An unbounded `max` MUST contribute no upper-bound clause to the encoding
  and MUST render without an upper bound in the report, so implementations emit the same
  script. ⟦s13|`min` MUST be a non-negative integer and a bounded `max` MUST be an integer at least
  `min`; a call of the `QuiescentCount` constructor function (named under Implementation notes) breaking either MUST be
  rejected where it is made, as the language reports a caller's error, rather than yield a verdict. A value built
  without that function, such as a Rust enum literal or a TypeScript object literal, is not checked.⟧ `min = 0` with `max` unbounded holds on every marking: an
  implementation MAY skip its query and SHOULD then report that it did, so a skipped clause is
  distinguishable from one that passed.
- **NameAligned(S)** and **QuiescentNameAligned(S)**, for a non-empty list `S` of coloured places:
  the places of `S` together hold at most one distinct name, in every reachable marking or in every
  reachable quiescent one. They read token names, so only Route B decides them and no other route
  gives them a verdict ([NU-055]).

The two sink-sensitive properties are not ordered by strength; they **invert on the empty
marking**. A quiescent `{done:1, stuck:1}` with `done` a sink violates DeadlockFree (it
strands `stuck`) but satisfies TerminatesAtSink. The fully drained marking `{}` satisfies
DeadlockFree (nothing is stranded) but violates TerminatesAtSink (no sink was reached).
Neither subsumes the other, which is why both exist.

⟦s14|The verifier *shall* read a marking as quiescent exactly when every transition whose enablement check ([NU-020]) passes on it is reapable, and, under `assumeNoReaping`, exactly when no transition's enablement check passes on it.⟧

⟦s15|*When* the verifier decides `DeadlockFree`, it *shall* report a marking as a violation exactly when the marking is quiescent and some marked place of it is stranded in the sense of [VER-014].⟧

⟦s16|*When* the verifier decides `TerminatesAtSink`, it *shall* report a marking as a violation exactly when the marking is quiescent and no declared sink holds a token.⟧

⟦s17|*When* the verifier decides `MutualExclusion` over a list of places, it *shall* report a marking as a violation exactly when two entries of the list, at different positions, hold a token.⟧

⟦s18|*When* the verifier decides `PlaceBound(place, k)`, it *shall* report a marking as a violation exactly when the place holds more than `k` tokens.⟧

⟦s19|*When* the verifier decides `Unreachable` over a non-empty list of places, it *shall* report a marking as a violation exactly when every listed place holds a token.⟧

⟦s20|*When* the verifier decides `QuiescentCount(places, min, max, waivedBy)`, it *shall* report a marking as a violation exactly when the marking is quiescent and either the tokens across `places`, each place counted once, number fewer than `min` while every `waivedBy` place is empty, or they number more than a bounded `max`.⟧

⟦s21|*If* the `QuiescentCount` constructor function is called with a `min` that is negative or not a whole number, or with a `max` that is not a whole number or is below `min`, *then* the call *shall* be rejected where it is made.⟧

⟦s22|*When* the `QuiescentCount` constructor function is called with a whole non-negative `min` and a `max` that is unbounded or a whole number at least `min`, the call *shall* yield the property with those bounds.⟧

**Acceptance Criteria:**
1. Each property can be constructed and passed to the verifier.
2. Properties are verified against the net's reachable state space.
3. **DeadlockFree** reports a violation for a quiescent marking that marks a declared sink
   while also holding a token in a non-sink place.
4. **DeadlockFree** reports no violation for the empty quiescent marking, whether or not
   sinks are declared. A net that drains completely has stranded nothing.
5. **TerminatesAtSink** reports no violation for a quiescent marking that marks any
   declared sink, regardless of tokens held elsewhere.
6. **TerminatesAtSink** reports a violation for the empty quiescent marking when at least
   one sink is declared.
7. Every route that decides these properties decides the **same** predicate: the SMT route
   ([VER-001]) and the ν name-partition state-class graph route ([VER-012]) return the same
   verdict for every marking both can classify.
8. **QuiescentCount** reports a violation for a quiescent marking below `min` while no
   `waivedBy` place is marked, and for one above `max` whether or not one is. A marking below
   `min` with a `waivedBy` place marked is not a violation.
9. **QuiescentCount** with a negative or non-integral `min`, or a non-integral `max` or one
   below `min`, is rejected at construction. Two implementations given the same unbounded `max` emit the same
   script, whatever each stores for it.
10. **MutualExclusion is pairwise on every route.** On `t: s → a + b` with `c` declared and
    never marked, from `{s: 1}`, `MutualExclusion([c, a, b])` is `Violated` with the trace
    `[t]` on the enumeration route, the linear bound, the VER-018 / VER-019 phases and the
    fixpoint query alike; on the chain `s → a → b → c` from `{s: 1}`, `MutualExclusion([a, b,
    c])` is `Proven` on each. `MutualExclusion([c, c])` on the chain is `Violated`, and
    `MutualExclusion([c])` is `Proven`. (Implementations taking exactly two places pass the
    two-place cases.)
11. **Reap-quiescence.** On `p0 → t → p1` with `t` at `window(3, 5)`, one token on `p0` and
    `p1` a sink, `DeadlockFree` is `Violated` with the empty trace (the initial marking is
    quiescent: only the reapable `t` is enabled), on the [VER-018] phase and on the fixpoint
    query alone; `TerminatesAtSink` is `Violated` the same way. With `assumeNoReaping` both are
    `Proven` and the report says the verdict assumes no transition is reaped. The quiescence
    clause of the HORN script leaves `t` out; a `PlaceBound` script is the same either way.
12. **Shadowed reapable transition.** The same net with an `immediate` `u: p0 → p1` added is
    `DeadlockFree` `Proven`: wherever `t` is enabled so is `u`, which cannot be reaped.
13. **No structural proof across a reap.** The self-loop `t: a → a` at `window(3, 5)` from
    `{a: 1}` with the enumeration off is `DeadlockFree` `Violated` with the empty trace, never
    `Proven` by the structural route; with `assumeNoReaping` it is `Proven`.
14. **Route B.** The same-mint join of [VER-012] with the join at `window(50, 200)`, `merged` a
    sink, is `DeadlockFree` `Proven` when nothing is reapable and `Violated` after the fork when
    the join is: a late executor reaps it with both branches marked. Under `Conflict` priority
    semantics the result is the same.
15. **Route B reads a late executor.** Beside the same-mint join of [VER-012], `t1: p → a` at
    `deadline(5)`, `window(3, 5)` or `exact(5)` and `t2: p → b` at `delayed(10)`, from
    `{p: 1, source: 1}`: `Unreachable([b])` is `Violated` on Route B with a trace ending in
    `t2`, and the report names `t1` as a transition whose latest bound was dropped. With
    `assumeNoReaping` it is `Proven`, and the report says the verdict assumes an on-time
    executor. With `t1` at `delayed(5)` nothing is dropped, and the report is the same with or
    without the option.
16. **Every quiescence route.** The AC11 witness is `DeadlockFree` `Violated` on the [VER-019]
    firing bound with the [VER-018] phase off, and on the [VER-018] phase with the firing bound
    off. On Route A ([NU-053]), the same-mint join at `window(50, 200)` with the fork consuming
    one budget token, `merged` a sink and Route B capped at one class, is `DeadlockFree`
    `Violated`; with `assumeNoReaping` it is not `Violated`.

**Implementation notes:**
- QuiescentCount: TypeScript `quiescentCount(places, min, max, waivedBy)` (unbounded `max` is
  `Infinity`); Python `quiescent_count(places, min, max, waived_by=None)` (`math.inf`,
  `ValueError` on a negative or fractional bound or `max < min`); Rust
  `SmtProperty::quiescent_count(places, min, max, waived_by)` (`Option<usize>`, panics on
  `max < min`); Java `SmtProperty.quiescentCount(places, min, max, waivedBy)` (`OptionalInt`,
  `IllegalArgumentException` on a negative `min` or `max < min`). Java and Rust SHOULD use an
  absent optional rather than a sentinel, so no count can collide with it. No shared fixture
  pins it yet.

**Test derivation:** For each property type: construct net where property holds → Proven; construct net where property is violated → Violated. The AC10 nets on the four route setups of the conformance suite. AC11 and AC12 are the shared parity fixtures `reaping-window-deadlock-violated`, `reaping-window-no-reaping-proven` and `reaping-shadowed-deadlock-free`, scripts pinned.

**Depends on:** [TIME-013] (reapable transitions)"#
