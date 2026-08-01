# `lean/` — machine-checked soundness of the verifier's abstraction

A Lean 4 development targeting one question: **is the SMT verifier's untimed
abstraction actually an over-approximation of the executor's semantics?**

Every false-`Proven` bug in the project's history — `667e67d`, `a4038f5`,
`c23cd9e` (NU-052), `98b9297` (VER-006), NU-051 — is a case where it was not.
That failure mode is the worst one available: the verifier answering "safe"
about an unsafe net.

This is deliberately **not** a formalization of the engine. The recent executor
bugs (`dc7bf83`, `a097001`: sync-throw containment, `Out.Timeout` context
lifetime, cross-thread `marking()`, lifecycle) are runtime plumbing that no
proof of the firing rule can reach, and the pure firing-rule bugs were
structural field drops at rebuild seams (`bindActions` / `rebuild_with_name` /
`mergeTransitions` losing `match_spec`) plus a JavaScript int32 sign-bit bug —
all of which a true proof would have sat beside, unbothered.

## Build

```bash
cd lean
lake build                  # a few seconds; no dependencies
```

Toolchain is pinned in `lean-toolchain` (Lean 4.32.2). There is **no Mathlib
dependency**: `α` erases colours to token counts, so every abstract marking is
ℕ-valued and core `Nat`/`List`/`omega` suffice. CI runs `lake build`, a
`sorry`/`admit` grep, and a `#print axioms` check on the headline theorems.

## What is proved

`Libpetri/Soundness.lean` — **Proposition 1**, `α(R(N)) ⊆ R(N̂)`
(`theory/verification-preserving-neural-substitution.typ`, where it is a proof
sketch). `proposition_one` is the reachability statement; `prop1_step` is the
simulation lemma carrying it.

It holds under two side conditions, and **the shipped encoder checks neither**.
Both are shown necessary by a concrete decidable counterexample, so neither is
proof bureaucracy:

### Finding 1 — a consume-all arc must be unguarded — **resolved by removing guards**

`GuardFreeConsumeAll`, witness `guard_hypothesis_is_necessary`.

**Status: discharged.** Input guards have since been deleted from Rust and TypeScript
(they were already absent from Java, and `IO-006` had tombstoned them in 2026-02 —
the implementations were drift from an unfinished breaking change). With no per-arc
predicate left, `GuardFreeConsumeAll` holds vacuously for every net that can now be
built, so Proposition 1 applies unconditionally on this axis and the encoder has
nothing left to be blind to.

The model below is kept deliberately: it is the evidence that motivated the removal,
and the record of what the abstraction could *not* have been made sound against.

`net_flattener.rs` never inspects an input arc's guard, so the encoder emits
`m'_i = post[i]` — place emptied — for every `In::All` / `In::AtLeast` place
(`smt_encoder.rs:165-167`). The executor consumes only guard-*matching* tokens
(`bitmap_backend.rs:644-652`, `count_matching` + `remove_matching`), so
guard-failing tokens survive the firing.

Concretely: place holds `[1, 2]`, guard accepts only `1`. The executor leaves
one token; the abstraction says zero. The abstract successor is *smaller* than
the concrete one, which is how `PlaceBound` gets a false `Proven`.

It was reachable through the documented API in Rust (`all_guarded`) and TypeScript
(`all(place, guard)`), with Python inheriting Rust's. **Java was never affected** —
its `Arc.In` records carried no guard field, because `6558113` had already removed
them there. So this was a two-verifier gap, not three.

### Finding 2 — an action writes at most one token per output place

`UnitOutput`, witness `unit_output_hypothesis_is_necessary`.

`validate_out_spec` (`executor_core/output.rs:19`) is a **set-membership**
check — it verifies *which* places the action wrote to, never how many tokens
it wrote to each. So an action satisfying `Out::Place(p)` may write any number
of tokens to `p`, while `net_flattener.rs:85-88` fixes the abstract gain at one
token per branch place (`all_places` returns a `HashSet`).

Neither paper states this condition. Paper A's Assumption W1 ("observationally
pure with respect to the marking") constrains side channels, not output
multiplicity, so it does not imply it.

## What is retrodicted

The acceptance criterion for this spike: the model must have enough resolution
to see defects that really happened, not just restate the paper.

`Libpetri/Priority.lean` — **`c23cd9e` (NU-052)**. `PrioritySemantics::Conflict`
*removes* transitions from the analysed relation, so it can only lose behaviour;
Paper A step 4 states priorities are not encoded, so Theorem 2 never covers this
mode. `preFixPrune` (before the `willFire` guard) and `postFixPrune` (shipped)
are separated by `willFire_guard_is_necessary`: a base-enabled but name-disabled
ν join out-competes the orphan drain, so the pre-fix condition prunes a firing
the executor really does perform.

`Libpetri/Retrodict.lean` — **`98b9297` (VER-006)**.
`envless_reach_is_trivial` proves that without the injection rule the reachable
set is exactly `{M₀}`, so `false_proven_without_injection` establishes
`PlaceBound(p₁, 0)` vacuously; `injection_reaches_violation` shows the bound is
violated once `smt_encoder.rs:81-83`'s injection rule is present.

## Scope

**In:** untimed fragment, all five arc kinds, input cardinalities, XOR
flattening, environment places, conflict-priority pruning.

**Out:** timing / DBM / Berthomieu–Diaz state classes; the ν name layer beyond
the boolean `nameEnabled` abstraction in `Priority.lean` (so the ν-budget
retrodictions `667e67d` and `a4038f5` are **not** covered — they need budget
conservation stated over real names, and are the first follow-on); Lemma 0
quiescence; extraction to the four implementations.

**Modelling assumptions**, each stated in the source where used:

- At most one input arc per place per transition (`specAt`). The flattener sums
  `required_count` over duplicates; nets with two input arcs on one place are
  outside the model.
- Concrete firing is specified at token-count granularity (`alphaFireC`,
  `StepC`), which is all `α` observes.

## Fidelity

A model that drifts from the encoder proves nothing about the encoder. Every
definition carries a doc comment naming the exact shipped function and line it
models. If one of those functions changes, this development is wrong until the
comment is rechecked — that is the maintenance obligation this directory adds.

Nothing in `theory/` is edited by this development; the papers are read-only
reference for the theorem statements.
