import Libpetri.Spec.Text

requirement_text VER_006
  id "VER-006"
  title "Environment Analysis Mode"
  priority SHOULD
  kind B
  body r#"The verifier supports configurable treatment of environment places during analysis:

- **AlwaysAvailable** — environment places are assumed to always have tokens (unbounded external input)
- **Bounded(k)** — at most k tokens **resident** in each environment place at a time: injection
  refills the place up to k, forever, so a transition can take at most k tokens from it per
  firing but the total injected over a run is unbounded. This is the executor only when no
  transition deposits into an environment place and the initial marking holds at most k on each
  one (AC3)
- **Arrivals(k)** — at most k tokens injected into each environment place **in total**, over the
  whole run
- **Arrivals(min, max)** — between `min` and `max` tokens injected into each environment place in
  total: `min` of them are required, the rest optional. `Arrivals(k)` is `Arrivals(0, k)`, and
  `Arrivals(k, k)` is exactly `k`. A configuration with `min < 0` or `max < min` is rejected when
  the mode is built, and a mode value written directly (a Rust enum variant) is refused before any
  route runs
- **Ignore** — environment places are not modeled

The default mode of the SMT verifier is `AlwaysAvailable`, and this requirement binds that
verifier and every route it dispatches to. The state-class graph API takes `AlwaysAvailable`,
`Bounded(k)` and `Ignore`, defaults to `Ignore`, and refuses `Arrivals`, which only the SMT
verifier applies, as a net rewrite.

**Arrivals is a net rewrite, not an encoding.** Before any route runs, the verifier closes the
net with the construction [VER-022] uses for an arrival group with the same `min` and `max`
(`min = 0`, `max = k` for `Arrivals(k)`): environment place `P`, the `i`-th registered (from 0, in
registration order), gets a mandatory source place `env:arrivals[i]` holding `min` tokens with an
injection transition `env:arrive[i]:P`, and an optional source place `env:optional[i]` holding
`max − min` tokens with an injection transition `env:arrive?[i]:P` and a transition
`env:decline[i]` with no output that discards a token of it. Each injection transition moves one
token from its source onto `P`. A source whose count is 0 is omitted with its transitions, exactly
as the [VER-022] closure omits it, so `Arrivals(k)` has no mandatory source and `Arrivals(k, k)`
no optional one. `P` stays in the net as an ordinary place. A run may rest only once every
mandatory arrival has happened, and after any number of optional ones: "between min and max"
holds for quiescence properties as well as for safety, once the undelivered optional arrivals are
declined. In particular, under `Arrivals(k, k)` a quiescent marking has seen exactly `k` arrivals,
which is what exact accounting on an open subnet ("k inputs arrive ⇒ k outcomes at quiescence")
needs; under `Arrivals(k)` a run that declines is always a counterexample to it. The rewritten net has **no** environment places,
so every route applies to it as to any closed net: the enumeration route ([VER-017]), P-invariants
and quiescence mean what they mean on a closed net, none of the `Ignore` refusals below applies,
and the vacuity note below arises only as it does on a closed net, from a transition that is not
reapable and has no input, read or inhibitor arc. Consequences a caller sees:

- Counterexample traces name the injection transitions (`env:arrive[i]:P`, `env:arrive?[i]:P`),
  each firing being one arrival, and the declines (`env:decline[i]`); the report says the net was
  closed under `Arrivals`, in the form `arrivals(k)` when `min = 0` and `arrivals(min..max)`
  otherwise, with the same wording in every implementation. P-invariants range over the rewritten
  net, sources included.
- A name the rewrite would add that the net already declares is rejected, as in [VER-022].
- The injected tokens carry names no analysis knows. An injection transition producing into a
  coloured place ([NU-051]) is **not** a mint: the ν routes ([NU-050] Route A, [VER-012] Route B)
  MUST NOT classify it as one, because two arrivals may carry one name and a mint would make them
  distinct, which can hide a reachable join (an unsound `Proven`). When an injected place is
  coloured, the ν routes decline with `Unknown` naming the place, exactly as AC8 does under
  `AlwaysAvailable`.

⟦s1|In `AlwaysAvailable` and `Bounded(k)` the verifier MUST **model external injection**: a
transition gated on an environment place becomes reachable (the SMT encoding emits an
injection rule that produces tokens into each environment place; under `Bounded(k)` injection
is capped).⟧ ⟦s2|Equivalently, the environment place is treated as an inexhaustible (or k-capped)
external source rather than a column that starts empty and can only be consumed.⟧ ⟦s3|Conservation
laws (P-invariants) derived from the closed net MUST NOT be applied to injected environment
places, since injection breaks closed-net conservation.⟧

**The mirror-image vacuity.** Under `AlwaysAvailable`, and under `Bounded(k)` when the cap
meets the demand, an input or read arc on an environment place is no reason a transition is
disabled. A transition with no inhibitor arc whose every input and read arc is such an arc has no
reason left: it is enabled, through injection, in *every* marking, so **no marking is quiescent**
and every quiescence property (`DeadlockFree`, `TerminatesAtSink`, `QuiescentCount`,
`JoinedOrDeadLettered`) is unviolatable. A transition that also needs a token of an ordinary
place, or carries an inhibitor arc, keeps a reason, so quiescent markings can exist beside it. The
`Proven` this yields is correct
and carries no information about the net: an open net with an always-available source never
comes to rest, so "no reachable quiescent marking strands a token" holds whatever the net does.
Unlike the `Ignore` case this is not refused, because the verdict is true; but an implementation
MUST report it, so a caller cannot read the empty claim as a guarantee about their workflow.
`QuiescentNameAligned` ([NU-055]) is the exception: where no marking can be quiescent it is
`Unknown` (AC6). Under a mode that models injection an environment place is an ordinary place for
the rest set of [VER-014]: a token left on it is stranded unless the caller declares the place a
sink, as the closure of [VER-022] does.

Because `Ignore` does not model injection, a safety property that holds **only** because
environment-gated transitions never fire is vacuous, and the verifier cannot tell which properties
hold only for that reason. When environment places are registered and the mode does not model
injection (`Ignore`), the verifier MUST NOT return `Proven` for any property: it reports `Unknown`
(with a reason) instead of silently certifying.

This binds **every route that can return `Proven`**, not only the SMT encoding. An
implementation that decides some properties structurally — the name-partition state-class graph
of [NU-050], say — reaches a verdict without ever building an encoding, and a structural
exploration under `Ignore` treats an environment place as an ordinary place that simply starts
empty. The bound it certifies then holds for exactly the reason this requirement rejects. Only
`Proven` is refused. A `Violated` of a reachability-safety property (`MutualExclusion`,
`PlaceBound`, `Unreachable`) under `Ignore` is a real counterexample in a strictly smaller
reachable set, so it is a fortiori a counterexample in the injected one. A `Violated` of a
quiescence property under `Ignore` is a rest of the net while the environment stays silent, which
need not be a rest under `AlwaysAvailable` or `Bounded(k)`: on `env IN → T → OUT` the empty
marking marks no sink, so `TerminatesAtSink({OUT})` is `Violated` under `Ignore`, while under
`AlwaysAvailable` no marking is quiescent and the property is `Proven` with the vacuity note.

⟦s4|*While* the mode is `AlwaysAvailable`, the verifier *shall* treat as reachable every marking the executor reaches while the environment injects tokens into the environment places.⟧

⟦s5|*While* the mode is `Bounded(k)` and the two premises of AC3 hold, the verifier *shall* treat as reachable every marking the executor reaches while the environment keeps at most `k` tokens resident in each environment place.⟧

⟦s6|*While* the mode is `Bounded(k)`, the verifier *shall* not treat as reachable a marking that holds more than `k` tokens on an environment place, from an initial marking that holds at most `k` on each one.⟧

⟦s7|*While* the mode is `Bounded(k)`, the premise check *shall* pass exactly when the initial marking holds at most `k` tokens on each registered environment place and no transition deposits into one.⟧

⟦s8|*If* the mode is `Bounded(k)` and the premise check fails, *then* the verifier *shall* return `Unknown` naming the environment place and the broken premise, and *shall* run no route.⟧

⟦s9|*While* the mode is `AlwaysAvailable` or `Bounded(k)`, an input or read arc on an environment place *shall* not count as a reason a transition is disabled, unless the mode is `Bounded(k)` and the arc demands more than `k` tokens, in which case the transition *shall* count as permanently disabled.⟧

⟦s10|*While* the mode is `AlwaysAvailable` or `Bounded(k)`, the verifier *shall* treat a marking as quiescent exactly when every transition that is not reapable is permanently disabled or has a disabling reason that holds at the marking.⟧ ⟦s11|A marking quiescent in this sense that is reachable with injection, from an initial marking that holds at most `k` tokens on each environment place under `Bounded(k)`, enables no transition, and no sequence of injections makes it enable one.⟧

⟦s12|The verifier *shall* report the vacuity note only for a quiescence property, and only when some transition of the verified net that is not reapable is neither permanently disabled nor has a disabling reason left under the mode, an input or read arc on an environment place being a reason under `Ignore` and `Arrivals`, which model no injection, and an inhibitor arc that the terminal rewrite of [EXEC-042] adds being a reason in every mode.⟧

⟦s13|*While* the mode is `AlwaysAvailable` or `Bounded(k)` and environment places are registered, *when* the property is a quiescence property and some transition of the verified net that is not reapable is neither permanently disabled nor has a disabling reason left (an inhibitor arc that the terminal rewrite of [EXEC-042] adds is a reason), the verifier *shall* report the vacuity note with a `Proven` or `Violated` verdict.⟧

⟦s14|*While* the mode is `Arrivals(min, max)`, the verifier *shall* verify the net closed with a mandatory source holding `min` tokens and an optional source holding `max − min` tokens for each environment place, so that a marking of the net is reachable in the closed net exactly when the environment reaches it with at most `max` arrivals on each environment place, and is a dead marking of the closed net exactly when it is reached with at least `min` arrivals on each environment place and enables no transition of the net.⟧

⟦s15|*If* environment places are registered and the mode is `Ignore`, *then* the verifier *shall* not return `Proven`, on any route.⟧

⟦s16|*When* the mode is `Ignore` and the verdict is `Violated` with `counterexampleConfirmed` `true`, the trace *shall* be a firing sequence of the verified net without injection to a marking that violates the property.⟧

**Acceptance Criteria:**
1. Each mode is selectable via the verifier configuration.
2. `AlwaysAvailable` allows broader reachability (more states): for a net `env IN → T → OUT`,
   `PlaceBound(OUT, k)` is `Violated` for every finite k (OUT is reachable and unbounded).
3. `Bounded(k)` limits the state space: a transition requiring more than k tokens from an
   environment place per firing is never enabled. This holds against the executor only under two
   premises: no transition deposits into a registered environment place, and the initial marking
   holds at most k on each one. Every route relies on both. The flat encoding caps each successor
   at k on an environment place, the state-class graphs enable an environment input exactly when
   it demands at most k whatever the place holds, and the quiescence clause calls a demand above k
   permanently disabled. Outside the premises the executor can hold more than k there, so a
   `Proven` can miss a firing and a `Violated` can report a rest the executor never reaches.
   Before any route the verifier checks both premises. When one fails it returns `Unknown`, naming
   the environment place and the broken premise (the initial count, or the first depositing
   transition in code-point order, named as the caller wrote it: a completion step
   `complete:<t>` of the in-flight split ([VER-004]) is reported as `t`), and runs no route. For `t0: a → E`, `t1: exactly(2, E) → out`
   under `Bounded(1)` with `M0 = {a: 2}`, `PlaceBound(out, 0)` is `Unknown`, not `Proven`, on the
   flat path and on Route B. For `tQ1: exactly(2, E) → out`, `tQ2: out → out` with `M0 = {E: 2}`,
   `DeadlockFree` is `Unknown`, not `Violated`.
4. `Ignore` with registered environment places never returns `Proven` (reports `Unknown`).
5. AC4 holds on every route the implementation offers, including any structural or state-class
   route that returns a verdict without invoking the solver.
6. When injection makes some transition enabled in every marking, a quiescence property is
   reported as vacuously true: the verdict stands, and the report names the reason.
   `QuiescentNameAligned` ([NU-055]) is the exception: it is `Unknown` instead.
7. The name-coloured encoding of [NU-050] Route A has no injection rule, so under
   `AlwaysAvailable` or `Bounded(k)` with environment places it MUST NOT answer: the query
   takes the flat encoding, which models injection, and the report says so. For a ν-net
   `env source → fork (mint) → join → merged` with a declared budget, `Unreachable(merged)` is
   `Violated` under both modes.
8. The name-partition state-class graph of [NU-050] Route B models an environment place under
   `AlwaysAvailable` / `Bounded(k)` only as an inexhaustible (k-capped) input: never consumed,
   never injected into, carrying no injected names. Its count in a state class is therefore not
   the environment's. When a Route B verdict would depend on that count or name layer, Route B
   MUST return `Unknown` naming the environment place, never `Proven`: the property reads an
   environment place (a quiescence property only when quiescence is reachable), an inhibitor arc
   tests one, an environment place is coloured (a match key or carrier), or conflict priority
   prunes on an environment input two transitions consume. Otherwise its verdict stands, and a
   quiescence verdict carries the AC6 note. For the ν-net
   `env IN, slot → fork → A, B → join (match) → accepted → ack → slot` under `AlwaysAvailable`,
   `PlaceBound(IN, 0)` is `Unknown` and `Unreachable(accepted)` is `Violated`.
9. `Arrivals(k)` bounds the total: for `env IN → T → OUT`, `PlaceBound(OUT, k)` is `Proven` and
   `PlaceBound(OUT, k − 1)` is `Violated` with a trace of `k` `env:arrive?[0]:IN` firings
   interleaved with `T`, while under `Bounded(k)` both are `Violated`. `DeadlockFree` with `OUT` a
   sink is decided without the AC6 vacuity note.
10. Under `Arrivals(k)` with a coloured environment place (a match key), no ν route returns a
    verdict that treats the injection transition as a mint; the ν routes decline naming the place.
11. `Arrivals(min, max)` requires the mandatory arrivals: for `env IN → T → OUT` with `OUT` a sink,
    `QuiescentCount({OUT}, 2, 2)` is `Proven` under `Arrivals(2, 2)` and `Violated` under
    `Arrivals(2)`, with a trace through `env:decline[0]`. `Arrivals(k)` and `Arrivals(0, k)` give
    the same verdicts, traces and scripts. `min < 0` and `max < min` are rejected.

**Implementation notes:** Java `EnvironmentAnalysisMode.arrivals(int)` and
`arrivals(int min, int max)`; TypeScript `arrivals(maxTokens)` and `arrivals(min, max)` beside
`bounded(maxTokens)`; Rust `arrivals(max_tokens)` and a two-bound form beside `Bounded`, keeping
`arrivals(k)` source-compatible; Python `libpetri.arrivals(max_tokens)` and
`libpetri.arrivals(min_tokens, max_tokens)` beside `bounded(max_tokens)`, passed as
`environment_mode=`. Each implementation reuses its [VER-022] closure code for the rewrite rather
than restating it. `Arrivals(k)` is selectable on
the verifier and in `SubnetDef.verify` ([MOD-051]).

**Depends on:** [VER-002], [VER-003], [VER-004], [VER-012], [VER-014], [VER-017], [VER-022], [NU-050], [NU-051], [NU-055]

**Test derivation:** Same net (`env IN → T → OUT`) with different environment modes; verify
`AlwaysAvailable` → `Violated`, `Bounded(k)` gates by per-firing multiplicity, `Arrivals(k)` bounds
the total (AC9), `Arrivals(k, k)` requires every arrival (AC11), `Ignore` → `Unknown`.
For AC5, a ν-net with an environment place and no declared budget place (which routes to the
state-class graph rather than the solver) under `Ignore`: a bound that is unreachable only because
injection was not modelled reports `Unknown`, not `Proven`. For AC8, the witness net above under
`AlwaysAvailable` and `Bounded(1)`: a bound on the environment place reports `Unknown`, and the
reachable `accepted` is `Violated`. For the AC3 premises, under `Bounded(1)`: a net whose initial
marking holds 2 on the environment place, and a net with a transition that deposits into it, each
report `Unknown` naming the place, with and without a ν-join beside them (the flat path and Route
B), while the same net with 1 on the place and no deposit keeps its verdict."#
