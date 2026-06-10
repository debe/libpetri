# 12 — ν-nets: Correlated Fork / Join by Identity

This document specifies **ν-net** capability: tokens carrying an opaque
correlation **name**, transitions that **mint** fresh names (the ν-binder), and
transitions that **join** by **name equality** across their inputs. Together
these express *fork a unit of work into parallel branches, then re-merge exactly
the siblings that belong together* — without smuggling correlation through
mutable external state (which would reintroduce the TOCTOU hazards CTPN exists to
avoid).

The design adds back the single **decidable** predicate — equality of opaque
names — as a *structural* cross-input constraint (like cardinality), NOT a
general guard. Arbitrary value predicates were removed in [IO-006]; ν-matching
does not reintroduce them (see the note under [IO-006]).

---

## Name Identity

#### NU-001: Name Identity

**Priority:** MUST

A **name** (`NameId`) is an opaque correlation identity. The only operation
defined on names is **equality**. A total order over names exists solely for the
deterministic match tie-break ([NU-020]) and carries no domain meaning.

Identity is a **projection of the token payload**, not a field on the token: a
[NU-020] match (or the analyzer) declares a `value → NameId` key. The token model
([CORE-010]) is unchanged — no name field is added — so event ([EVT-011],
[EVT-012]) and archive formats are unaffected.

**Acceptance Criteria:**
1. Two names constructed from the same underlying value are equal; from
   different values, unequal.
2. Names admit a stable total order consistent across a single implementation.
3. Adding ν-matching to a net does not change the token type or the on-the-wire
   shape of token-bearing events.

**Test derivation:** Construct `NameId("a")` twice; verify equal. Verify
`NameId("a") < NameId("b")`. Verify a net with no match spec emits identical
token events with and without the ν-net APIs linked.

---

## ν-binder (Fork)

#### NU-010: Fresh-Name Minting

**Priority:** MUST

A transition action MAY mint a fresh name via the action context
(`ctx.freshName()` / `ctx.fresh_name()`). The action writes the minted name into
the payloads it produces, so the sibling tokens of a fork (an [IO-011] AND
output) share one correlation name.

Minted names MUST be unique across all firings of a single execution and SHOULD
be deterministic for a fixed firing order (replay stability). The executor
installs the minter; absent an executor-installed minter, a fallback still
guarantees uniqueness.

**Acceptance Criteria:**
1. Two `freshName()` calls — within one firing or across firings — return
   unequal names.
2. A fork that stamps both AND-branches with one minted name produces sibling
   tokens that a [NU-020] join later correlates.
3. For a fixed firing order, the sequence of minted names is reproducible.

**Depends on:** [CORE-050], [IO-011]
**Test derivation:** A `fork` transition mints a name per firing and stamps both
output branches; with three source tokens, verify three distinct names reach the
downstream join and each pair merges (see `nu_fork_mints_unique_ids_then_join_merges`).

---

## Join by Name Equality

#### NU-020: Match Specification

**Priority:** MUST

A transition MAY declare a **match specification**: a subset of its **input**
places, each with a `value → NameId` key projection. Every place named by the
match MUST also be a declared input. The match adds a correlation requirement on
top of the existing input cardinalities ([IO-001]–[IO-004]):

- **Enablement** = the usual cardinality/bitmap/inhibitor checks ([CORE-022])
  **and** there exists a single name `n` present in *every* correlated input
  with at least that input's required count of key-projecting-to-`n` tokens.
- **Firing** consumes, for the chosen `n`, the matched tokens from each
  correlated input (FIFO within a name); non-correlated inputs consume FIFO as
  usual ([EXEC-010]).

**Determinism (tie-break).** When more than one name satisfies the join, the
implementation MUST choose by this exact rule, so all languages fire identically:
1. the name whose **oldest matched token** (minimum `createdAt` across the
   correlated inputs) is **earliest**;
2. ties broken by **name order** ([NU-001]).

> The name-order tie-break is byte-identical across implementations for **BMP**
> names (which covers every executor-minted name, `"{transition}#{n}"`). For
> supplementary-plane code points in a user-supplied key, Rust's code-point order
> can differ from the Java/TypeScript UTF-16 code-unit order; [NU-001] requires
> only per-implementation consistency, which holds.

**Acceptance Criteria:**
1. A join correlates by name, not arrival order: with branch A = [X@t0, Y@t1] and
   branch B = [Y@t0, X@t1], the join produces the X-X and Y-Y pairings, never X-Y.
2. With no name present in all correlated inputs, the join is not enabled; its
   input tokens remain.
3. A correlated `Exactly(k)` / `AtLeast(m)` input requires k / m tokens **of the
   matched name**; `All` consumes all tokens of the matched name.
4. The tie-break selects the earliest-oldest name, then the lexicographically
   least name, identically across implementations.

**Depends on:** [IO-001], [IO-005], [CORE-022], [CORE-013]
**Test derivation:** `nu_join_matches_by_name_not_fifo` (reversed arrival),
`nu_join_blocks_without_matching_name`, mirrored across every executor in every
language.

---

#### NU-021: Guard / Match Composition

**Priority:** MUST

Where an implementation also supports a unary input filter on a correlated input,
the filter applies **first** and the name correlation runs over the survivors. A
token must pass the filter *and* project to the chosen name to be consumed.

**Acceptance Criteria:**
1. A correlated input with both a unary filter and a key consumes only tokens
   that pass the filter and carry the chosen name.
2. The order is fixed (filter, then match) and observable: a token failing the
   filter is never consumed even if its name matches.

**Depends on:** [NU-020]
**Test derivation:** A correlated input filtered to even values, joined by name;
verify an odd token of the matched name is left behind.

#### NU-022: Deterministic Match Selection

**Priority:** MUST

When more than one correlation name is simultaneously eligible at a matched
transition, the implementation MUST select the name with the smallest
`(oldest correlated-token timestamp, then NameId)` ordering: oldest first, ties
broken by name. The selection is a pure function of the current marking and MUST
be **identical across all conforming implementations**: the firing tie-break
(`selectMatchName` / `select_match_name`) is byte-identical, and any incremental
acceleration of it MUST return byte-identical results to the reference function.

**Acceptance Criteria:**
1. Given the same eligible *(name → correlated-token timestamps)* state, every
   implementation selects the same `NameId`.
2. An incremental matcher returns the same `NameId` as the reference
   `selectMatchName` for any sequence of add/consume operations.
3. `NameId` ordering is byte-identical for ASCII/BMP names (all executor-minted
   names are ASCII); supplementary-plane code points MAY order differently per
   [NU-001] (UTF-8 byte order vs UTF-16 code-unit order).

**Depends on:** [NU-020], [NU-001]
**Test derivation:** A randomised differential test (`MatchEngineIncrementalTest`,
`incremental_matches_select_byte_for_byte`, `incremental-matcher.test.ts`) asserts
the incremental `best()` equals `selectMatchName` over non-monotonic timestamps.

---

## Composition

#### NU-030: Freshness Scoping under Composition

**Priority:** MUST

ν-name freshness is **per instance**, as a structural consequence of name
prefixing ([MOD-012]): the executor mints names qualified by the firing
transition's (post-compose, instance-prefixed) name, so two instances of the same
subnet draw from disjoint name pools with no extra runtime state. A match
specification carried through composition MUST have its correlated places
remapped by the same place rewrite the arcs follow ([MOD-020]), so a composed
join still correlates the renamed inputs.

**Acceptance Criteria:**
1. Two instances of a forking subnet never mint colliding names.
2. After composition, a join's match correlates the renamed (host-bound) places,
   not the author-original ones.

**Depends on:** [MOD-010], [MOD-012], [MOD-020]
**Test derivation:** Instantiate a fork+join subnet twice; verify each instance's
joins merge only their own siblings.

---

#### NU-060: Match-Arc Composition

**Priority:** SHOULD

A correlated input behaves, under channel composition ([MOD-021]), as the input
arc it layers on: its arc dedup/conflict rules are unchanged. When two merged
sides both carry a match on the same place, the implementation MUST either fuse
to a single coherent correlation or reject the merge naming the conflict; it MUST
NOT silently drop a match.

**Acceptance Criteria:**
1. Composing a transition that carries a match preserves the match on the flat
   net (it is not dropped).
2. A merge that would combine two incompatible matches on one place is rejected
   with a diagnostic, or fused deterministically.

**Depends on:** [MOD-021], [NU-020]
**Test derivation:** Channel-merge a matched transition with a passthrough side;
verify the composed transition still correlates.

---

## Decidability — the bounded-budget ledger

#### NU-040: Bounded Budget and Decidability

**Priority:** SHOULD

Be explicit about the cliff. **Safety / coverability** for the ν-fragment is
**decidable** [RV-08]: the marking-with-names state space is a well-structured transition
system. Full **reachability / liveness** with *unbounded* fresh names and
*unbounded* recirculation is **undecidable** in general (ν-PN reachability is
undecidable [RV-11]).

A **bounded budget** is the decidability lever, not merely operational hygiene.
Model it structurally: a typed `Budget` place pre-seeded with `k` tokens whose
single token a fork consumes when it mints a name and a join (or a dead-letter
transition) returns. Then:

- "at most `k` live correlation groups" is the structural invariant
  `PlaceBound(Budget, k)` ([VER-002]) — checkable with the existing untimed
  encoder, no name reasoning required;
- a `Pending` place (one token per live group, emptied only by join or
  dead-letter) plus `PlaceBound(Pending, k)` and quiescence ([EXEC-040]) to
  `Pending = 0` expresses **"every forked name is eventually
  joined-or-dead-lettered."**

With the budget bounded and branch places `PlaceBound`-checked, fresh names are
drawn from a finite live pool, the WSTS stays finite, and these properties become
provable. This is the [reask/retry-budget-as-typed-place] discipline applied to
correlation.

**Acceptance Criteria:**
1. A fork gated on a `Budget` input cannot mint more than `k` concurrently-live
   names; `PlaceBound(Budget, k)` holds.
2. A net whose every forked name is joined or dead-lettered reaches `Pending = 0`
   at quiescence; `PlaceBound(Pending, k)` holds.
3. The spec states plainly that without a bounded budget, reachability/liveness
   over unbounded fresh names is undecidable and the verifier returns `Unknown`
   for that case ([NU-050]).

**Depends on:** [VER-002], [EXEC-040], [NU-010], [NU-020]
**Test derivation:** Build a scatter-gather net with a `Budget(k)` place; verify
`PlaceBound(Budget, k)` and `PlaceBound(Pending, k)` with the untimed encoder.

---

#### NU-050: Exact Verification of Matched Transitions

**Priority:** MAY

The untimed encoder over-approximates guards ([VER-004]). For ν-nets this is
relaxed under a carve-out: a matched transition's **name equality** is encoded
**exactly** rather than name-blind, so a counterexample that silently equates two
*different* names (criterion **#1** below) is ruled out. The name dimension is the
projection declared at the match ([NU-001]) — the analyzer treats it as
name-symmetric.

The exactness goal MAY be realized by either of two routes:

- **Route A — bounded name-colouring** (the budget made literal). Because a
  bounded `Budget` ([NU-040]) caps the live correlation groups at `k`, names are
  modeled as a finite set of `k` **colours**: each coloured place becomes `k`
  per-colour counts, a mint introduces a *globally fresh* colour, and a join
  consumes the **same** colour from every correlated input. Within the budget
  this is sound *and complete* (exact), and stays in linear arithmetic. It
  applies to the **mint → matched-join fragment**: coloured places (the matched
  inputs) are produced only by minting forks and consumed only by matched joins,
  each mint costs a budget token, **budget is conserved across a mint→join pair**
  (a join refunds no more budget than the cheapest mint consumes, so the live
  colours stay ≤ the initial budget `k`), and coloured places carry no
  inhibitor/read/reset arc. A net outside this fragment — including one whose join
  refunds more budget than its mint consumes — falls back to the sound
  over-approximation (criterion #1 then holds only where the exact route was taken).
- **Route B — SCG name-partition** (implemented). A **state-class-graph quotient
  partitioned by name relations**: each correlation token carries an abstract,
  interchangeable name-*symbol*, a matched join fires only on a name shared by
  every correlated input, and the graph is quotiented under name-permutation
  symmetry (the canonical key abstracts the symbol identities, which is what keeps
  it finite without a budget). This generalises the exactness **beyond the bounded
  fragment** — to budget-less but structurally name-bounded nets, to **name × time**
  (the DBM firing zone rides alongside the name partition), and to **quiescence**
  (deadlock / joined-or-dead-lettered, decided over the name-aware terminal
  classes). It is sound, and exact (sound *and* complete) whenever the symbolic
  graph closes within the class bound; an unbounded live-name pool surfaces as
  graph truncation → `Unknown` (never an unsound verdict). The alternative
  realization — equality over an uninterpreted **name sort** (EUF) in the CHC
  encoder — is not taken (the SMT path is untimed, and Spacer over an
  uninterpreted sort is poorly supported).

When the live correlation-name pool is **not bounded** — no budget ([NU-040]) and
no structural bound the name-partition quotient (Route B) can discover — the
verifier MUST return `Unknown` rather than an unsound verdict (criterion **#2**
below, mirroring the `Ignore`-mode discipline of [VER-006]); under Route B this
appears as state-class-graph truncation.

**Acceptance Criteria:**
1. (**NU-050 #1**) A property whose counterexample requires two *different* names
   to be equal is not reported on the exact path, unlike the over-approximated
   guard case.
2. (**NU-050 #2**) An unbounded-fresh-name net without a budget place yields
   `Unknown`, not `Proven`/`Violated`.

**Depends on:** [VER-004], [NU-020], [NU-040]
**Test derivation:** Encode a join whose spurious untimed counterexample equates
two distinct correlation ids; verify the exact carve-out (Route A bounded
name-colouring) eliminates it, while a same-name join still reaches its merge.

---

## Implementation Notes

- The selection + tie-break ([NU-020]) is a single algorithm shared by both
  executor backends in each language and ported verbatim across languages
  (Rust `match_engine::select_match_name`, Java/TS `MatchEngine.selectMatchName`),
  so firing order is byte-identical.
- A transition with no match spec pays nothing: enablement and consumption take
  the existing fast path; the match path is gated on a per-transition flag.
- Python (`libpetri-py`) inherits the Rust runtime; the key projection is a
  Python callable evaluated under the GIL per candidate token, and `ctx.fresh_name()`
  delegates to the executor-installed minter.
- The bounded-budget lever ([NU-040]) is verified through two dedicated safety
  properties — `BranchPlaceBound(place, k)` (a budget/branch count bound) and
  `JoinedOrDeadLettered(pending)` (no reachable quiescent marking holds a
  `pending` token) — alongside the existing `PlaceBound`. The verifier is told
  which place gates minting via a **budget-place declaration**
  (`budget_place(s)` / `budgetPlaces(...)`); this is what asserts the bounded
  fragment.
- The sound **over-approximation baseline** (the name-blind CHC encoding) cannot
  decide two cases soundly: a ν-net with no declared budget (unbounded fresh
  names), and any **quiescence-based** property (deadlock-freedom,
  joined-or-dead-lettered) on a ν-net — whose violation turns on the *absence* of
  an enabled join, which over-firing distorts. The verifier routes exactly those
  cases (and timed ν-nets) to the **Route B** name-aware state-class graph; only
  when Route B also cannot bound the live-name pool (graph truncation) does the
  verdict remain `Unknown`.
- The [NU-050] exact carve-out (**Route A — bounded name-colouring**) is
  implemented for the **mint → matched-join fragment** of a budget-declared
  ν-net: there, reachability-safety properties are decided *exactly* (sound and
  complete within the budget `k`) — no spurious different-name counterexample —
  so neither `Proven` nor `Violated` carries the over-approximation caveat. A
  budget-declared ν-net **outside** that fragment falls back to the sound
  over-approximation: a reachability-safety `Proven` is sound (the real net fires
  strictly fewer joins) and a `Violated` is flagged as possibly spurious pending
  the fuller [NU-050] analysis.
- The [NU-050] **Route B** exact analysis (the **SCG name-partition quotient**) is
  implemented in all four bindings (Rust is the source of truth; Python inherits
  it through `verify`; Java and TypeScript port it byte-faithfully, sharing the
  canonical name-partition key format). It decides reachability-safety **and**
  quiescence over the mint → matched-join fragment **without requiring a declared
  budget** (finiteness comes from the name-permutation symmetry quotient), and
  composes with the timed firing domain (name × time). It is solver-free (it does
  not invoke Z3). The verifier keeps Route A's bounded name-colouring as the
  primary path for budget-declared, untimed reachability-safety (Z3 IC3 scales
  there) and uses Route B for the cases the SMT path cannot decide exactly —
  quiescence, budget-less ν-nets, and timed ν-nets.

---

## References

ν-nets implement the **ν-Petri net** (ν-PN) model — place/transition nets
extended with *pure name creation* (the ν-binder) and name management — and
inherit its decidability frontier: coverability is decidable while reachability
is undecidable. [NU-040] and [NU-050] navigate that frontier with the
bounded-budget lever and the name-aware state-class graph.

- **[RV-08]** F. Rosa-Velardo and D. de Frutos-Escrig. *Name Creation vs.
  Replication in Petri Net Systems.* Fundamenta Informaticae 88(3):329–356, 2008.
- **[RV-11]** F. Rosa-Velardo and D. de Frutos-Escrig. *Decidability and
  Complexity of Petri Nets with Unordered Data.* Theoretical Computer Science
  412(34):4439–4451, 2011. doi:10.1016/j.tcs.2011.05.007
