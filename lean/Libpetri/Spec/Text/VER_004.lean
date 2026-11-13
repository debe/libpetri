import Libpetri.Spec.Text

requirement_text VER_004
  id "VER-004"
  title "Untimed Over-Approximation"
  priority SHOULD
  kind B
  body r#"SMT verification operates on untimed Petri net semantics (marking projection, integer token counts). Timing only restricts which firings happen: every timed firing is an untimed one, and a reap ([TIME-013]) changes no marking, so every marking a timed run visits is reachable in the untimed net (Lean `ReapingVsUntimed.timed_markings_reachable`). A proof of a property of the marking alone on the untimed net therefore holds for the timed net (`marking_properties_transfer`).

Timing does add one thing the untimed net lacks: a place to **rest**. A late executor reaps a `Deadline` or `Window` transition and stops at a marking that still enables it, a marking the untimed net does not count as quiescent (`reaping_refutes_ver004_ac3`: `p0 → t → p1`, `t = window(3, 5)`, rests at `{p0}` with the token stranded while the untimed `DeadlockFree` is `Proven`). The untimed abstraction MUST include this, so every quiescence property reads quiescence reap-aware ([VER-002]): a marking where every enabled transition is reapable counts as quiescent. With that reading, a proof on the untimed net is sound for every timed run, a late one included. `assumeNoReaping` restores the plain reading; a `Proven` under it holds only for an on-time executor, one that reaps no transition and lets no armed transition pass its latest bound, and the report says so.

**Atomic firings and in-flight actions.** Every route reads a firing as one atomic step: its inputs leave and its outputs arrive in the same step. The executor does not fire that way. It consumes a firing's inputs when the action starts and deposits the outputs when the action completes ([EXEC-001] steps 5 and 1), and it fires other transitions in between. An asynchronous action keeps that gap open while it runs ([CONC-002]). A synchronous one keeps it open to the end of its firing pass, because a drain later in the same pass does not see the deposit ([EXEC-003] AC5). For monotone arcs the gap changes nothing: a run with `t` in flight can be reordered so that `t`'s deposit follows its start at once, because the steps in between only see more tokens in `t`'s output places, and a transition that needs tokens stays enabled and does the same. It does change something when a transition tests one of `t`'s output places **non-monotonically**: an inhibitor arc, a reset arc, or a draining input (`all`, `atLeast`). A terminal place ([EXEC-042]) counts too, since it inhibits every transition. With `t: one(p) → p` and an async action, and `u: one(q) + inhibitor(p) → bad`, `p` is never empty in any atomic run from `{p, q}`, so `Unreachable(bad)` was `Proven`; the executor fires `u` while `t` is in flight. With `start: one(req) + inhibitor(busy) → busy` and two requests, `PlaceBound(busy, 1)` was `Proven` too, and two guarded transitions sharing `busy` both start.

The untimed abstraction MUST therefore model the two-step firing for every transition `t` with an output place (in any branch, the `Timeout` branch included) that some transition tests non-monotonically. Such a `t` is **split** into:
- `t` itself, with every input, read, inhibitor and reset arc, its timing, priority and match spec, whose only output is a fresh place `inflight:<t>`, and
- `complete:<t>`, `immediate()`, with the one input `one(inflight:<t>)`, no other arc, `t`'s priority and `t`'s output spec, in which a `forwardInput(from, to)` leaf deposits into `to`.

Two readings split more transitions, because the property or the priority semantics tests the gap too:
- A `QuiescentCount` with `min > 0` on a net with a terminal place it does not waive ([EXEC-042]) splits every transition that deposits into a counted place or a waiver place. A terminal stop abandons an action in flight, so the counted tokens it would deposit never arrive.
- Conflict priority on Route B ([NU-052]) splits every pruning transition `H` (one with strictly higher priority than another it shares a consumed input with) and every transition that deposits into an input or read place of `H`. A pruner pre-empts nothing while `inflight:<H>` is marked. If one of these transitions cannot be split (below), the verifier turns conflict priority off for that call, explores every enabled transition, and the report says which transition could not be split.

The completion step directly follows `t` in the transition order, and the in-flight places follow the net's own places in the order of the split transitions. Every other transition stays atomic, so a net with no such transition is verified, and scripted, exactly as before ([VER-013]). The split comes before the terminal rewrite of [EXEC-042], so a terminal also inhibits each completion step and excuses each in-flight place. A marked in-flight place never rests: its completion step is enabled, immediate and not reapable. A transition that models the environment rather than an action of the net (the arrivals of [VER-006], the environment of an open-net contract, [VER-022]) stays atomic. The completion step is itself one deposit and is never split again.

The split cannot express three cases, and a verifier MUST then answer `Unknown` on every route, naming the transition: a transition to split that is a ν-join, or that writes a coloured place (a match key, a relay target or a declared carrier), since its halves would lose the name the output carries ([NU-010], [NU-020], [NU-054]); a `Timeout` that forwards an `exactly(n)`, `all` or `atLeast` input, whose token count ([IO-014]) the completion step cannot see; and a net that already uses a name the split would add. An implementation MUST offer the opt-out `assumeAtomicFiring` (`assume_atomic_firing`), which reads every firing as one step; the report of a net the split would change then states the assumption, and conflict priority keeps pruning. Tokens an action publishes before it completes (`ctx.flush()`, Rust and Python) are not modelled for a split transition: its completion step deposits every output at once, and the report of every split verdict says so.

The split lets `t` start again while `inflight:<t>` is marked, which the Rust executor does and the Java and TypeScript executors never do ([CONC-002]). ⟦s1|That is a sound over-approximation for all three.⟧ A `Violated` whose trace starts `t` while `inflight:<t>` is marked MUST say so in its report, naming `t`, since on Java and TypeScript such a trace may be a false alarm:

```
NOTE (CONC-002): the counterexample starts 'start' again while its earlier firing is still in flight (inflight:start marked). The Rust executor starts a transition again while its action runs; the Java and TypeScript executors never do, so on them this counterexample may be a false alarm.
```

Completeness does not hold: a counterexample in the untimed abstraction may be a run the timing forbids. Such a `Violated` stands, because the untimed claim is the contract; [VER-003]'s `counterexampleTiming` says what the counterexample means for the timed net, and the opt-in check of [VER-023] asks the timed state-class graph, without ever changing the verdict.

The encoding is additionally **value-blind**: it carries token counts, not token values. Every value-dependent choice — which XOR branch an action writes to, which token a correlated input picks — is therefore over-approximated as freely available, which is also sound for safety properties. (There is no value-predicate construct left to approximate: guards were removed in [IO-006].)

**ν-net carve-out.** The over-approximation is relaxed for the one *decidable*
predicate. A matched transition's name equality ([NU-020]) MAY be encoded
**exactly** as equality over an uninterpreted name sort (EUF) while token counts
stay in linear integer arithmetic — see [NU-050]. This removes spurious
counterexamples that would require two distinct correlation names to be equal,
without sacrificing soundness, and is the one place the untimed encoder reasons
about token *identity* rather than only token *counts*.

⟦s2|Each firing the executor takes under its timing *shall* be a firing of a transition of the untimed net, from the same marking to the same marking.⟧

⟦s3|A reap ([TIME-013]) and the passing of time *shall* change no marking.⟧

⟦s4|*Where* the transitions of a net have distinct names, a marking at which a timed run from the initial marking ([TIME-010]) rests, with no transition it enables armed, *shall* be quiescent as [VER-002] reads quiescence by default: every transition it enables is reapable.⟧

⟦s5|*Where* the transitions of a net have distinct names, a marking at which an on-time run from the initial marking ([TIME-010]) rests, one that reaps no transition and lets no armed transition pass its latest bound, *shall* enable no transition.⟧

⟦s6|A place is tested non-monotonically when it is a terminal place, when some transition has an inhibitor arc, a reset arc or an `all` or `atLeast` input on it, or when one of the two readings below counts it so.⟧

⟦s7|*If* the property is a `QuiescentCount` with `min > 0` and the net has a terminal place its waiver places do not name, *then* the verifier *shall* count the property's places and its waiver places as tested non-monotonically.⟧

⟦s8|*While* conflict priority applies, the verifier *shall* count the input and read places of every pruning transition, one with strictly higher priority than another transition that shares an input place with it, as tested non-monotonically.⟧

⟦s9|*While* `assumeAtomicFiring` is not set, the verifier *shall* split exactly the transitions that model no environment, are not a completion step (a transition named `complete:<x>` whose one input is `one(inflight:<x>)` and that has no read or reset arc), and either are pruning transitions while conflict priority applies or have an output place, in any branch with the `Timeout` branch included, that is tested non-monotonically.⟧

⟦s10|The verifier *shall* replace each split transition `t`, at its position in the transition order, by `t` with every input, read, inhibitor and reset arc and its timing, whose only output is the place `inflight:<t>`, directly followed by `complete:<t>`, `immediate()`, whose one input is `one(inflight:<t>)`, which has no other arc, and whose output spec is that of `t` with each `forwardInput(from, to)` leaf replaced by the place `to`.⟧

⟦s11|The places of the split net *shall* be the places of the net followed by `inflight:<t>` for each split transition `t` in the transition order, and every transition that is not split *shall* stay as it is.⟧

⟦s12|*If* no transition is to be split, *then* the verifier *shall* verify the net as it is.⟧

⟦s13|*If* a transition to split is a ν-join, writes a coloured place, has a `Timeout` that forwards an input whose cardinality is not `one`, or would add a name the net already uses for a place or a transition, *then* the verifier *shall* refuse the split with a reason that opens with `transition '<t>'` for the first such transition `t` in the transition order, and *shall* answer `Unknown` on every route.⟧

⟦s14|*While* `assumeAtomicFiring` is not set, *if* conflict priority applies, the net has a pruning transition, and a transition the verifier would split under conflict priority cannot be split, *then* the verifier *shall*, instead of refusing the split, turn conflict priority off for that call and split the net as it does without conflict priority.⟧

⟦s15|*While* `assumeAtomicFiring` is set, the verifier *shall* verify the net as it is and *shall* keep conflict priority as it applies.⟧

⟦s16|*While* `assumeAtomicFiring` is not set and the split succeeds, *where* no firing fails (no action fails, and output validation and the relay check reject no output or timeout outcome), no action publishes an output before it completes and no token is injected, a marking the executor reaches from the initial marking, with each action in flight of a transition that is not split completed with one of its outcomes, *shall* be reachable in the split net from the initial marking, with one token on `inflight:<t>` for each action of a split transition `t` in flight.⟧

**Acceptance Criteria:**
1. The flat routes read no timing bound: of a transition's timing they read only whether it is
   reapable ([VER-002]). Route B ([VER-012]) keeps each earliest bound, and each latest bound only
   under `assumeNoReaping`.
2. Verification is value-blind — value-dependent branch and correlation choices are
   over-approximated (except the [NU-020] name-equality carve-out of [NU-050], when
   implemented).
3. A Proven verdict on the untimed net implies the property holds for all timed executions,
   including those of an executor that runs late and reaps a transition ([TIME-013]), with
   quiescence read as [VER-002] defines it. Under `assumeNoReaping` a Proven verdict holds for
   the timed executions of an on-time executor, in which no transition is reaped and no armed
   transition passes its latest bound, and the report states that assumption. On Route B
   ([VER-012]), which keeps the latest bounds under `assumeNoReaping`, a firing is also one
   instant step, so the verdict holds only for an executor whose actions take no time. The
   report says so, and a closed graph is called exact only for such an executor: with `t: a →
   p` at `deadline(20)` and a 150 ms action, `h: p + b → ok` at `deadline(20)` and `v: b → bad`
   at `delayed(60)`, beside a ν pair, `Unreachable(bad)` is `Proven` under `assumeNoReaping`
   with that label, `Violated` by default, and the executor marks `bad`.
4. A Proven verdict holds for the executor's runs with actions in flight whose actions publish no
   output before they complete (no `ctx.flush()`): every transition
   whose output some transition tests non-monotonically is verified as its start and
   `complete:<name>`, and the report names the split transitions. From `{p, q, go}`, with
   `t: one(p) + one(go) → p` whose action is asynchronous, `u: one(q) + inhibitor(p) → r` makes
   `Unreachable(r)` `Violated`, and `u` with `reset(p)`, `all(p)` or `atLeast(2, p)` instead
   makes `MutualExclusion(p, r)` `Violated` (from two and three tokens on `p` for the two
   drains). The executors reach the same markings.
5. A net with no such transition produces byte-identical scripts, with or without
   `assumeAtomicFiring`.
6. A ν-join or coloured writer that needs the split, and a `Timeout` forward from an input that is
   not `one` that needs it, give `Unknown` on every route, naming the transition. Under
   `assumeAtomicFiring` the net is verified atomically and the report states the assumption.
   Under conflict priority a transition that cannot be split turns the pruning off instead:
   the verdict is the one without conflict priority, and the report names the transition.
7. With `t: one(a) → p` (async), `H: p + b → ok` at priority 10, `L: b + inhibitor(a) → bad` at
   priority 0, and a declared ν pair, from `{a, b}`, `Unreachable(bad)` under conflict priority
   is `Violated` and the report names `t` and `H` as split; the executors mark `bad`. Under
   `assumeAtomicFiring` it is `Proven` with the assumption in the report.
8. The guard net `start: one(req) + inhibitor(busy) → busy` from two requests gives a report
   with the CONC-002 note naming `start`; a net whose trace starts no transition while it is
   in flight has no such note.

**Test derivation:** Net with timing constraints; verify property on the untimed abstraction; verify same property holds in timed execution. For AC3, the [VER-002] AC11 witness: `DeadlockFree` is `Violated` at the initial marking, which is where a late executor rests; `Proven` only under `assumeNoReaping`, with the assumption in the report. For AC4, run each net on both executors with an action that sleeps, confirm the executor reaches the marking, then verify it on the enumeration route and on the SMT pipeline alone (`enumerationMaxClasses(0)`); `start: one(req) + inhibitor(busy) → busy` from two requests gives the trace `start, start, complete:start, complete:start`. Disable the split and confirm each test fails.

**Depends on:** [TIME-013], [EXEC-001], [EXEC-003], [EXEC-042], [CONC-002], [NU-052]"#
