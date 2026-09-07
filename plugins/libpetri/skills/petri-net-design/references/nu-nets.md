# ν-nets reference: correlated fork and join by identity

Spec: `spec/12-nu-nets.md` (NU-001..NU-060) inside a libpetri checkout, otherwise
https://github.com/debe/libpetri/blob/main/spec/12-nu-nets.md.

## Contents

1. [The problem ν solves](#1-the-problem-nu-solves)
2. [Identity is a projection, not a field](#2-identity-is-a-projection-not-a-field)
3. [Minting and matching](#3-minting-and-matching)
4. [The tie-break is normative](#4-the-tie-break-is-normative)
5. [The budget place is the decidability lever](#5-the-budget-place-is-the-decidability-lever)
6. [When to use ν and when plain structure is better](#6-when-to-use-nu-and-when-plain-structure-is-better)
7. [Fragment rules the exact routes require](#7-fragment-rules-the-exact-routes-require)
8. [Verifying a ν-net](#8-verifying-a-nu-net)

---

## 1. The problem ν solves

Fork one unit of work into parallel branches, then re-merge **exactly the siblings that belong together**, while several groups are in flight at once.

The usual answer outside this model is a correlation map: each branch result carries a request id, and the join transition's action looks the id up in a concurrent map to see whether all siblings have arrived. That is a check-then-act gap. Two branches can observe an incomplete group at the same instant, and the window is exactly where the race lives.

ν-nets put the correlation **in the firing rule**. Enablement itself requires that every correlated input holds tokens of one common name. There is no interval between deciding and acting, because deciding *is* acting. That is the whole point, and it is why the correlation is also visible to the verifier.

## 2. Identity is a projection, not a field

A `NameId` is opaque. The only defined operation is equality. (A total order exists solely to make the tie-break deterministic and carries no meaning.)

Identity is declared at the match as a projection from the token payload: a `value -> NameId` key function. **No field is added to the token.** The token model is unchanged, event and archive formats are unaffected, and a net without a match spec pays nothing at run time.

Practical consequence: you do not restructure your domain types to adopt ν. When the payload already carries a correlation id, you point at the field you have (`order.id`, `req.correlationId`) and declare it as the key. When it does not, a fork mints one and writes it into the payload, which is the only case where a mint is warranted.

**Decide this before anything else: do the tokens already share an identity?**

- **They do** (every provider response already carries the request's `correlationId`, every row already carries the order id). Then **project it and do not mint**. A name is constructed from the underlying value, and two names built from the same value are equal (NU-001 AC1), so the field you already have *is* the identity. Nothing about your token types changes.
- **They do not** (the grouping comes into existence at the fork, and the branches would otherwise have nothing in common). Then the forking action mints one fresh name and **writes it into the payloads it produces** (NU-010), so the siblings share it. The match then projects that field back out.

Minting and projection are not alternatives. Projection is how a match reads identity, always. Minting is only how identity gets *into* the payload when the domain did not already supply it. Reaching for a fresh name when a correlation id is already in hand adds a field, adds a mint site you then have to declare as a budget place, and buys nothing.

## 3. Minting and matching

**Minting** (NU-010). An action mints a fresh name through the context (`ctx.freshName()`). Names are unique across all firings of one execution and replay-stable for a fixed firing order. The minter qualifies names by the firing transition's post-composition, instance-prefixed name, which means **freshness is per instance for free** (NU-030): two instances of the same forking subnet draw from disjoint pools with no extra runtime state.

**Matching** (NU-020). A match spec names a subset of the transition's **input** places, each with a key projection. Enablement is the ordinary cardinality, bitmap and inhibitor check **and** the existence of a single name `n` present in every correlated input with at least that input's required count of tokens keying to `n`.

Cardinality becomes per-name: a correlated `exactly(k)` needs k tokens *of the matched name*; a correlated `all()` consumes all tokens *of the matched name*. Non-correlated inputs consume FIFO as usual.

**A match spec must correlate at least two input places.** Building one over a single place is
rejected, and the reason is the design in one line: a match over one place correlates nothing, it is
just a guard, and guards were deliberately removed from this model. So "one shared results place
with `exactly(5)`, correlated" is not a thing you can build. Give each correlated stream its own
place, or correlate the one results place together with a second input such as the pending marker.

**Correlate every input of the join, not only the interesting ones.** A non-correlated input
consumes FIFO as usual, which means a join firing for group A can take group B's token from it. The
classic instance is a `pending` marker left unkeyed: the join then matches five responses of one
name against whichever pending token happens to be at the front. If an input takes part in the
commit, it takes part in the match.

**Name equality is the only per-token filter in the enablement check** (NU-021). This is not a reintroduction of guards, which were removed from the model deliberately. Everything else stays positional.

Correlation is checked after the bitmap and cardinality phases, so a net that never matches pays the cheap checks first.

## 4. The tie-break is normative

When several names could fire, choose the name whose **oldest matched token** (minimum creation time across the correlated inputs) is earliest; break ties by name order (NU-022). Any incremental matcher must return byte-identical results to the reference selection.

This matters because it makes replay and cross-language behaviour deterministic. Do not design a net whose correctness depends on a different tie-break, and do not assume "whichever arrived first at this place" when several inputs are correlated: it is the oldest token across the whole matched group that decides.

## 5. The budget place is the decidability lever

Safety and coverability for the ν fragment are decidable. Full reachability and liveness with unbounded fresh names are not. The lever is **structural**, not operational hygiene:

- A typed budget place pre-seeded with k tokens. The fork consumes one when it mints. The join, or a dead-letter transition, returns one.
- "At most k live correlation groups" then *is* the invariant `PlaceBound(budget, k)`, checkable by the ordinary untimed encoder with no name reasoning at all.
- A pending place (one token per live group, emptied only by join or dead-letter) plus a bound on it and quiescence with pending empty expresses **"every forked name is eventually joined or dead-lettered"**. That is the dedicated `JoinedOrDeadLettered` property. It is exactly *quiescent and `pending` at least 1* (NU-040): since the 5.0 wave it no longer inherits a sink clause from the deadlock predicate, which used to let any marked sink excuse a stranded correlation group and defeated the whole point of the property.
- With the budget bounded and branch places bounded, fresh names come from a finite live pool, the system stays finite, and these properties become provable.

**You must tell the verifier which place gates minting** (`budgetPlaces` / `budget_place(s)`). Declaring it is what asserts the bounded fragment. Without it, a minting net is treated as unbounded and you will get `Unknown`.

If you want a ν-net proved, give it a budget place. This is the single highest-value design decision in the whole ν feature.

## 6. When to use ν and when plain structure is better

Use ν when **all** of these hold:

1. several correlation groups can be in flight at the same time, **and**
2. their branch tokens share the same places, **and**
3. the join must pair the right siblings.

That is scatter-gather over N parallel calls, per-request fan-out, correlated retries.

Plain colours and cardinality are enough, and cheaper, when:

- **At most one group is structurally live at a time** (a budget of 1, or a mutex place). Then FIFO plus cardinality already pairs correctly.
- **Each group gets its own subnet instance**, so the branch places are already disjoint. Instance isolation is free at run time and cheaper to verify than a name partition.
- **The correlation id is only carried as payload** and never gates enablement.

**Do not declare a match spec you do not need.** It moves the query onto the ν routes and away from cheap linear-arithmetic IC3, and you pay for correlation reasoning you were not using.

## 7. Fragment rules the exact routes require

These are hard modelling constraints, not tuning knobs. Violating one does not produce a wrong answer, it produces a fallback to a coarser over-approximation, so the symptom is an `Unknown` or a stubbornly unprovable net.

- **No reset, read or inhibitor arc on any coloured place** (NU-051), in both fragment modes. Such an arc would be misclassified and drift the name layer from the base marking.
- **A coloured consumer (a drain or a relay) consumes exactly one coloured input at count exactly one.** Not `exactly(n>=2)`, not `at_least`, not `all`, and not two coloured inputs. Re-emitting a higher input cardinality into the name layer over-counts and could let a join fire by equating two distinct names, which is a false `Proven`.
- **Never consume and re-mint on the same transition.** A relay threads the consumed name into its coloured outputs, or into none of them (a drain). A single `Xor` transition may relay on one branch and drain on another.
- **Declare carrier places explicitly and spell them correctly.** A mistyped carrier must fail loudly (a builder rejection, or `Unknown` naming the place), never be ignored: silently ignoring it would let two fork branches mint independent names and yield a confident spurious deadlock verdict.
- **Budget conservation must not leak.** A join must refund no more budget than the cheapest mint consumes. The colour-slot bound comes from a covering non-negative P-semiflow over the coloured set. A fan-out that co-mints a colour into a place no matched join re-collects has no covering semiflow and falls back rather than certifying.

## 8. Verifying a ν-net

Two exact routes, plus a sound fallback:

- **Route A, coloured IC3/PDR.** Scales. Wants a declared budget and the clean mint-to-join fragment above. This is where budget-declared untimed safety queries go.
- **Route B, name-partition state-class quotient.** Solver-free. Names are interchangeable symbols, quotiented under permutation symmetry, which keeps the graph finite even without a budget. Exact over name and time, and it is the route that decides **quiescence**. It has no partial-order reduction, so heavy independent-branch parallelism truncates it.
- **The over-approximation fallback** is sound for reachability safety, but **not** for quiescence. A `Proven` on a quiescence property never comes from the fallback.

Routing in practice: a quiescence query, or a net with no declared budget, tries Route B first; if Route B truncates on a bounded quiescence query, the verifier defers to the coloured Route A encoder rather than giving up.

If a ν property comes back `Unknown`, work down this list: declare the budget place, check the fragment rules in section 7, reduce places shared between parallel branches, split independent work into separate subnet instances, and turn on the semiflow invariant option.
