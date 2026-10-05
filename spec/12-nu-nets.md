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

What replays is the sequence **within a minting scope** ([NU-011]). Under the
default scope the scope component of a name differs from run to run by design —
that is what keeps a resumed execution from re-minting a live name — so a host
that needs the *whole* name reproduced pins the scope, and a test compares names
structurally or pins one rather than hard-coding a default-scope name.

**Mint contract (verification).** An action may write any value into a match key, a
correlation id copied from its input included, and no analysis can tell a minting action
from a copying one: the stock `fork()` action copies its input. So the ν routes of
[NU-050] read a transition as a **mint**, one that writes a fresh name, only when the net
declares it, in one of two ways:

- by naming it as a mint transition on the verifier (`mintTransitions` /
  `mint_transitions`);
- by its consuming a declared budget place ([NU-040]), whose token is what a fork
  consumes when it mints.

A declared mint MUST write, into each coloured place ([NU-051], [NU-054]) it writes
without consuming one, a name it minted with `freshName()` in that firing. A transition
that writes a coloured place without consuming one and is not declared keeps the net off
both routes, and the verifier answers through the name-blind over-approximation. What
the executor writes on timeout ([IO-013], [IO-014]) is never a mint, declared or not: a
`ForwardInput` copies a consumed token, name included, and an `Out.Place` writes a unit
token, which has no name. A declared mint that is not a transition of the net MUST fail
loudly and name it, the same way at every entry point: verification, script encoding
([VER-013]) and open-net verification ([VER-022]), with the reason `declared mint transition
'x' not in the net (NU-010)`. Java throws where the mint is declared, the open-net hook
included. TypeScript throws where it is declared on a verifier, and open-net verification
answers `Unknown`. Rust answers `Unknown` from verification and open-net verification before
any route runs, and its script encoding panics; Python raises `ValueError` from script
encoding. The report
of a verdict from either route names the transitions whose mint contract it assumes. When
Route B declines a net only because a transition writes a coloured place without consuming
one and is not declared, the report names that transition and points at the declaration.

**Acceptance Criteria:**
1. Two `freshName()` calls — within one firing or across firings — return
   unequal names.
2. A fork that stamps both AND-branches with one minted name produces sibling
   tokens that a [NU-020] join later correlates.
3. For a fixed firing order and a fixed scope ([NU-011]), the sequence of minted
   names is reproducible.
4. (MUST, where the [NU-050] routes are offered) `mA: S1 → A` and `mB: S2 → B` with the stock `fork()`, and a join on `A`, `B` into
   `DONE`: with one correlation id in `S1` and `S2` the executor reaches `DONE = 1`, and
   `placeBound(DONE, 0)` is not `Proven` unless `mA` and `mB` are declared mints. Declared,
   it is `Proven` by Route B and the report names `mA, mB` under the mint contract.
5. (MUST, where offered) `t1: budget, reqA → xor(okA, timeout(20, forwardInput(reqA, a)))`, its twin `t2` into
   `b`, and a join on `a`, `b`: the executor forwards both requests on timeout and joins
   them when they carry one id. `placeBound(done, 0)` is not `Proven` on either route,
   with `t1` and `t2` declared or with `budget` a declared budget place.
6. (MUST, where offered) A declared mint that is not a transition of the net fails loudly and
   names it.

**Depends on:** [CORE-050], [IO-011], [IO-013], [IO-014], [NU-040], [NU-050]
**Test derivation:** A `fork` transition mints a name per firing and stamps both
output branches; with three source tokens, verify three distinct names reach the
downstream join and each pair merges (see `nu_fork_mints_unique_ids_then_join_merges`).

---

#### NU-011: Resume-Safe Fresh-Name Minting

**Priority:** MUST

[NU-010] scopes minted-name uniqueness to "a single execution". Restoring a marking
([CORE-073]) begins a **new** execution whose initial marking already holds names minted by
the previous one. An implementation that satisfies [NU-010] by counting firings from zero
therefore re-mints names that are already live — and because a [NU-020] join correlates on
name equality alone, the collision does not surface as an error: it silently correlates
tokens from different run segments, merging a restored token with an unrelated fresh one.

Names minted by an execution seeded from a restored marking MUST NOT collide with names
present in that marking, nor with names minted by any other execution in the same restore
lineage. The mechanism is not prescribed. Two that satisfy it:

- a per-execution **scope** supplied by the host and incorporated into every minted name;
- carrying the minter's high-water mark in the snapshot and resuming strictly above it.

**The restore lineage crosses processes.** [CORE-073] offers restore as a suspend boundary, a
durable checkpoint, a crash-recovery point — so the execution that resumes a marking is, in the
normal case, running in a *different process* from the one that minted the names in it. "Unique
per executor" read as "unique within a process" is therefore not enough. Anything derived from a
per-process counter restarts with the process, and the first executor of the new process re-mints
the first name of the old one: exactly the silent merge above, in the default configuration.

**The default scope MUST be unique across processes — and is therefore not the run identifier.**
Absent a host-supplied scope, an implementation using the scope mechanism — all four do — MUST
draw one per executor from the platform's random source: a 128-bit value rendered as exactly **32 lowercase hexadecimal characters**, of
which at least 122 bits are random (a version-4 UUID with its dashes removed conforms). The
rendering is fixed so that a default-scope name looks alike, and parses alike, in every language.

An earlier revision of this requirement said that an implementation which already publishes a run
identifier SHOULD default the scope to it, "so one value means one thing". **That SHOULD is
withdrawn**, because the two values are required to have opposite properties. A run identifier
SHOULD be *reproducible* for a fixed construction order ([TIME-015] AC#14) — that is what lets a
replay carry the same identifier, and it is what a per-process counter provides. A default scope
MUST *differ* between two processes that did nothing differently — which is precisely what a
reproducible value cannot do. One value cannot be both. The run identifier remains the
reproducible one, the default scope is the unique one, and an implementation MUST NOT derive
either from the other.

**The scope's uniqueness is required; its observability is not.** The default scope MAY be entirely
internal — an implementation is not required to publish it, on an event or anywhere else, and MUST
NOT be read as required to merely to satisfy this requirement. What a host can observe is the
*name*, and the property that matters is that two executors never mint the same one. An
implementation whose scope is internal therefore conforms exactly as one whose scope is visible,
and the difference is not a divergence in behaviour.

**The name format, and what a scope may contain.** An implementation using the scope mechanism
mints `<transition>#<scope>:<n>`, where `<n>` is a per-executor counter from zero. A host-supplied
scope MUST be rejected when the executor is configured — not at the first mint — if it is **empty**
or contains **`:`** or **`#`**; the separators are rejected rather than escaped. Two details are
fixed because the implementations otherwise drift apart on them:

- *Empty* means length zero. A whitespace-only scope is legal, if unwise; an implementation MUST
  NOT trim the scope or test it for blankness, since "blank" is defined differently by every
  standard library and the same configuration would then be accepted in one language and refused
  in another.
- Rejecting `:` alone is **not** enough. Transition `a` under scope `b#c` and transition `a#b`
  under scope `c` both mint `a#b#c:0` — a collision between two segments of one lineage, which is
  what this requirement forbids. With `#` banned as well, a minted name parses uniquely whatever
  the transition name contains: the **last `:`** splits off the counter, and the **last `#` before
  it** splits off the scope; everything in front is the transition name.

A pinned scope is host text, so it SHOULD stay within the Basic Multilingual Plane for the reason
given under [NU-020]'s tie-break; this is advice to the host, not a validation.

Deriving the floor by scanning the restored marking is **not** sufficient in general: name
carrying values are opaque to the engine ([VER-004]), and a name minted into a token that has
since been consumed leaves no trace in the marking while remaining live in host state and in
any token the host holds across the restore.

Replay stability ([NU-010] AC3) is preserved **within** a run segment: for a fixed scope (or
a fixed restored high-water mark) and a fixed firing order, the minted sequence MUST be
reproducible. Randomness is therefore admitted in exactly **one** place — the *default* scope,
chosen once per executor — and nowhere else: the counter `<n>` MUST NOT be random, and a scope
the host pinned MUST be used verbatim, with nothing random mixed into it or into the sequence
minted under it. A host that needs a reproducible segment pins its scope (AC3). A host that pins
nothing gets uniqueness instead of reproducibility, and that is the right default: an
unreproducible name is visible and harmless, a cross-segment merge is neither.

**Acceptance Criteria:**
1. Restore a marking holding a name `n` minted by a prior execution; run the resumed
   execution so it mints at least as many names as the original minted; no minted name
   equals `n`.
2. A restored token awaiting its sibling at a [NU-020] join is not correlated with a
   freshly minted token of the resumed segment.
3. For a fixed scope and firing order, two runs from the same restored marking mint the
   identical name sequence.
4. Two concurrent executions restored from the same snapshot mint disjoint name sets.
5. **The default scope is not process-local.** An executor given no scope mints names whose scope
   component is 32 lowercase hexadecimal characters, different for every executor and — where
   the implementation publishes a run identifier — not equal to it. AC1 and AC2 therefore hold
   when the resuming executor is the *first* one constructed in its process, which is the case a
   per-process counter fails.
6. **Scope validation and the parse rule.** An empty scope, a scope containing `:` and a scope
   containing `#` are each rejected at configuration; a whitespace-only scope is accepted. A name
   minted by a transition whose own name contains `#` and `:` splits back into transition, scope
   and counter by the rule above.

**Depends on:** [NU-010], [NU-020], [CORE-073], [TIME-015], [VER-004]
**Implementation status:** Implemented in all four, as `<transition>#<scope>:<n>`. The default
scope is a random 32-hex token drawn per executor — `crypto.randomUUID()` in **TypeScript** and
`UUID.randomUUID()` in **Java**, dashes stripped; 128 bits of the platform's random state in
**Rust**, which **Python** rides — and it is internal everywhere, so nothing was added to any
event and the session-archive decision stays open on its own terms. The run identifier
(`executionId` / `execution_id`) is a *different* value: it stays the reproducible per-process
counter of [TIME-015] AC#14. A host pins the scope (`executionScope` / `execution_scope`) for the
replay reproducibility of AC#3. Validation is the same in all four — length zero, `:` or `#` —
and is raised as the language's argument error (`IllegalArgumentException`, `Error`, Python
`ValueError` from both the binding and the `ExecutorOptions` wrapper); **Rust** panics, in
`set_execution_scope` and in every builder that takes a scope, and documents the panic on each.
**Test derivation:** Run a ν-fork net under a **pinned** scope until a token carrying a minted
name awaits its sibling at a join; snapshot and restore into a fresh execution under a different
pinned scope — and again under the default one; fire the fork and assert the new name differs
from the restored one and that the join does not merge the restored token with the new one.
Repeat the restore twice concurrently and assert the two name sets are disjoint. No test may
depend on how many executors the process constructed before it: compare names structurally
(transition, scope, counter) or pin the scope, and include a case in which the resuming executor
is the first one constructed.

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

A match names each correlated input once: the input's cardinality, not a repeated key, sets how
many tokens of the name it takes. Building a match or a transition whose match keys one place
twice MUST fail. Every correlated input requires at least one token ([IO-002], [IO-004]).

**Determinism (tie-break).** When more than one name satisfies the join, the
implementation MUST choose by this exact rule, so all languages fire identically:
1. the name whose **oldest matched token** (minimum `createdAt` across the
   correlated inputs) is **earliest**;
2. ties broken by **name order** ([NU-001]).

> The name-order tie-break is byte-identical across implementations for **BMP**
> names. An executor-minted name is `"{transition}#{scope}:{n}"` ([NU-011]): its
> default scope and its counter are ASCII, so it is BMP exactly when the
> transition name — and the scope, where a host pinned one — is. Both of those
> are host text and fall under the same caveat as a user-supplied key: for
> supplementary-plane code points, Rust's code-point order can differ from the
> Java/TypeScript UTF-16 code-unit order; [NU-001] requires only
> per-implementation consistency, which holds.

**Acceptance Criteria:**
1. A join correlates by name, not arrival order: with branch A = [X@t0, Y@t1] and
   branch B = [Y@t0, X@t1], the join produces the X-X and Y-Y pairings, never X-Y.
2. With no name present in all correlated inputs, the join is not enabled; its
   input tokens remain.
3. A correlated `Exactly(k)` / `AtLeast(m)` input requires k / m tokens **of the
   matched name**; `All` consumes all tokens of the matched name.
4. The tie-break selects the earliest-oldest name, then the lexicographically
   least name, identically across implementations.
5. A match that keys one place twice is rejected when the match is built, and when a
   transition is built with such a match from any other construction path (a bindings layer,
   a composition remap, an object literal).

**Depends on:** [IO-001], [IO-005], [CORE-022], [CORE-013]
**Test derivation:** `nu_join_matches_by_name_not_fifo` (reversed arrival),
`nu_join_blocks_without_matching_name`, mirrored across every executor in every
language.

---

#### NU-021: Match as the Sole Per-Token Filter

**Priority:** MUST

Name correlation ([NU-020]) is the **only** per-token filter the enablement check
applies. There is no unary value predicate on an input: guards were removed in
[IO-006] and no implementation carries one, so token selection is determined by
position ([EXEC-010], [IO-007]) and, on correlated inputs, by name equality —
nothing else.

Should a future revision reintroduce a unary input filter, the composition order is
fixed here in advance: the filter applies **first** and the name correlation runs
over the survivors, so a token must pass the filter *and* project to the chosen name
to be consumed. Until such a construct exists, this requirement is satisfied by the
absence of any competing filter.

**Acceptance Criteria:**
1. No input specification variant exposes a value predicate; the enablement check
   evaluates no per-token predicate other than name equality on correlated inputs.
2. A correlated input consumes only tokens carrying the chosen name; a same-place
   token of a different name is left behind regardless of its value.

**Depends on:** [NU-020], [IO-006]
**Test derivation:** A ν-join over a place holding tokens of two different names;
verify only the tokens of the selected name are consumed and the others remain.

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
3. `NameId` ordering is byte-identical for ASCII/BMP names (an executor-minted
   name is one whenever its transition name and any host-pinned scope are — the
   default scope and the counter are ASCII; [NU-011]); supplementary-plane code
   points MAY order differently per
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

Declaring a budget place to the verifier also declares the mint contract of [NU-010]
for every transition that consumes it: where such a transition writes a coloured place
without consuming one, the ν routes read the write as a fresh name.

**Acceptance Criteria:**
1. A fork gated on a `Budget` input cannot mint more than `k` concurrently-live
   names; `PlaceBound(Budget, k)` holds.
2. A net whose every forked name is joined or dead-lettered reaches `Pending = 0`
   at quiescence; `PlaceBound(Pending, k)` holds.
3. The spec states plainly that without a bounded budget, reachability/liveness
   over unbounded fresh names is undecidable and the verifier returns `Unknown`
   for that case ([NU-050]).
4. `JoinedOrDeadLettered(pending)` is exactly "no reachable quiescent marking holds
   a `pending` token". It carries **no sink clause**: declared sink places
   ([VER-002]) do not weaken it, and a stranded correlation group is a violation
   whether or not some sink happens to be marked in the same marking. Every route
   that decides it decides this same predicate.

**Depends on:** [VER-002], [EXEC-040], [NU-010], [NU-020]
**Test derivation:** Build a scatter-gather net with a `Budget(k)` place; verify
`PlaceBound(Budget, k)` and `PlaceBound(Pending, k)` with the untimed encoder.

---

#### NU-050: Exact Verification of Matched Transitions

**Priority:** MAY

The untimed encoder is value-blind ([VER-004]). For ν-nets this is
relaxed under a carve-out: a matched transition's **name equality** is encoded
**exactly** rather than name-blind, so a counterexample that silently equates two
*different* names (criterion **#1** below) is ruled out. The name dimension is the
projection declared at the match ([NU-001]) — the analyzer treats it as
name-symmetric.

The exactness goal MAY be realized by either of two routes:

- **Route A — bounded name-colouring** (the budget made literal). Because a
  bounded `Budget` ([NU-040]) caps the live correlation groups at `k`, names are
  modeled as a finite set of `k` **colours** (`k` is the colour-slot bound of [NU-053],
  at least the number of live names): each coloured place becomes `k`
  per-colour counts, a mint introduces a *globally fresh* colour, and a join
  consumes the **same** colour from every correlated input, so no counterexample
  equates two different names. It stays in linear arithmetic, and its `Proven` is
  sound while the declared mints and the coloured consumers keep their contracts
  ([NU-010], [NU-051]). It applies to the **mint → matched-join fragment**: coloured
  places (the matched inputs) are produced only by minting forks and consumed only by
  matched joins, each mint is declared ([NU-010]), **budget is conserved across a mint→join pair**
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

Under modelled injection ([VER-006]) Route B treats an environment place as an inexhaustible
input and so cannot observe its count or the names injected into it; it declines (`Unknown`)
when a verdict would depend on them ([VER-006] AC8).

On a timed net Route B gives a matched join a clock only while one name-symbol is present in
every correlated input, because the executor enables the join only then ([NU-020]). A join whose
inputs hold tokens but share no name has no clock, so its latest bound constrains no other
firing. The clock-restart rule of [TIME-012] reads the name layer too: a firing that takes the
bound name out of a correlated input restarts the join's clock even when the input still holds
tokens, and a join whose inputs come to share a name starts a fresh clock then. This holds with
and without the latest-bound relaxation for a late executor ([TIME-013]).

Route B reads every coloured token through one name. It assumes that each key and relay
projection reading a coloured place returns the name its writer put there: the name a mint
stamped, or the name a relay or consumer carried over. The analysis cannot inspect a projection,
so this is a contract on the net, like the mint contract of [NU-010]. Two projections that read
one place differently, or a projection that returns no name for a written token, fall outside
it.

Both routes read a coloured write as a fresh name only for a declared mint ([NU-010]), and as
the consumed name only for a coloured consumer ([NU-051]). A write the executor makes on timeout
is read by what it is: a forward carries the consumed token's name and a unit token has none.
Where no role reads a coloured write faithfully, the net is outside both routes.

**Acceptance Criteria:**
1. (**NU-050 #1**) A property whose counterexample requires two *different* names
   to be equal is not reported on the exact path, unlike the value-blind
   over-approximation.
2. (**NU-050 #2**) An unbounded-fresh-name net without a budget place yields
   `Unknown`, not `Proven`/`Violated`.
3. Two forks mint one name each into the two inputs of a join with `window(0, 5)`, and a
   watchdog marks `BAD` at `delayed(10)`. Route B reports `unreachable(BAD)` violated, on time
   and late: the join is never enabled, so its deadline does not hold back the watchdog.
4. A join at `delayed(10)` is count-enabled from 1 ms and first shares a name at 5 ms. Route B
   lets it fire at 15 ms at the earliest.

**Depends on:** [VER-004], [NU-020], [NU-040], [TIME-012]
**Test derivation:** Encode a join whose spurious untimed counterexample equates
two distinct correlation ids; verify the exact carve-out (Route A bounded
name-colouring) eliminates it, while a same-name join still reaches its merge.

---

#### NU-051: EXTENDED Coloured-Consumer Fragment

**Priority:** MAY

The [NU-050] Route B name-partition quotient decides the **mint → matched-join**
fragment exactly. An opt-in **EXTENDED** fragment mode widens that exact path to
two further shapes without weakening its soundness: a **coloured consumer**
(drain/relay) that removes a correlation name without a match, and **carrier
places** that thread a fork-minted name through intermediate places to a ν-join
input. The mode is a two-value knob — **BASE** (default) reproduces the shipped
mint → matched-join fragment exactly; **EXTENDED** is selected on the verifier
builder (`fragmentMode` / `fragment_mode`). Both are decided solely by the
solver-free Route B quotient; neither changes the canonical name-partition key
format ([VER-012]), so cross-language byte compatibility is preserved.

- **Coloured consumer (drain/relay).** Under EXTENDED, a transition with **no**
  match spec MAY consume a coloured place. The analyzer admits it only as a
  drain/relay role and only when it consumes **exactly one** coloured input at
  count **exactly one** ([IO-001] `One` or [IO-002] `Exactly(1)`). It **relays**
  the consumed name-symbol into each coloured output of the fired branch
  (threading the same name), or **drains** it (dead-letters the name) on a branch
  that produces no coloured output; a single `Xor` transition ([IO-012]) MAY relay
  on one branch and drain on another. Because the consumed count is fixed at one,
  the role is identified by the input place name alone — no count, no input list.
  A consumer that consumes more than one coloured place, or consumes at any count
  other than one (`Exactly(n≥2)`, `AtLeast`, `All`), is **rejected** to the sound
  over-approximation: the base marking adds exactly one token per output place, so
  re-emitting a higher input cardinality into the name layer would over-count and
  could let a join fire by equating two distinct names (a false `Proven`).

- **Relay/drain action precondition.** The coloured-consumer role is a modeling
  contract on the action, and MUST be documented as such. The action MUST thread
  the consumed correlation name into its coloured outputs (relay), or into **none**
  of them (drain); it MUST NOT mint a *fresh* name into a coloured output while
  consuming a coloured token. A consume-and-remint transition is **out of
  contract** for EXTENDED — the name layer would thread the consumed name where the
  runtime mints afresh, so this mode does not make such a net exact. Selecting
  EXTENDED is the declaration of this contract, and the report of a verdict names the
  consumers whose action writes it assumes. A write the executor makes on timeout is
  no action write: a timeout of a coloured consumer that writes a coloured place is a
  relay only when it forwards the consumed coloured input itself. A forward of another
  input copies a name the consumer did not consume, and an `Out.Place` writes a unit
  token with no name; either puts the net outside the fragment.

- **Carrier places (fork-threaded co-mint).** Under EXTENDED, an author MAY declare
  intermediate **carrier** places (`carrierPlaces` / `carrier_place(s)`) that carry
  a fresh name from the minting fork ([NU-010]) onward to a ν-join input. The
  analyzer unions the declared carriers into the coloured set **before** role
  assignment, so the existing mint co-mints one fresh name into all of them. A
  declared carrier name absent from the net's places MUST NOT be silently ignored:
  the implementation MUST fail loudly (reject at the builder, or surface `Unknown`
  with a reason naming the offending place), because a mistyped carrier would let
  two fork branches mint independent names and produce a confident, spurious
  deadlock verdict. Under BASE, declared carriers are ignored (a documented no-op).

- **Reset/read/inhibitor-on-coloured exclusion (BOTH modes).** In **both** BASE and
  EXTENDED, the analyzer rejects a net in which **any** coloured place carries a
  reset ([CORE-034]), read ([CORE-032]), or inhibitor ([CORE-031]) arc on any
  transition. Such an arc would be misclassified `Ordinary`, letting the base step
  zero or gate the coloured place while the name layer keeps the symbol, drifting
  the name layer from the base count marking. This is a deliberate soundness
  tightening applied to BASE too (rejection just falls back to the sound
  over-approximation); it never turns a `Proven`/`Violated` into an unsound verdict.

- **Off-key coloured input exclusion (BOTH modes).** In **both** BASE and EXTENDED,
  the analyzer rejects a net in which a matched transition consumes a coloured place
  through an input that is **not** one of its match keys. Such an input consumes
  FIFO ([NU-020]), whatever the token's name, so the name layer cannot know which
  name leaves the place: Route B would keep the symbol and Route A would force the
  join's shared colour on it. A non-coloured non-key input (a budget or permit) is
  unaffected. Rejection just falls back to the sound over-approximation.

- **Diagnosability.** When EXTENDED is requested but the net falls outside this
  fragment, the verifier MUST surface a short note (an "EXTENDED declined" line)
  rather than silently falling back, so an author can tell the exact path was not
  taken.

**Acceptance Criteria:**
1. (MUST) Under EXTENDED, a drain/relay fixture (a non-match transition consuming
   one coloured place at count one) classifies into the coloured-consumer role;
   under BASE the same net is rejected to the over-approximation.
2. (MUST) A coloured consumer that consumes at count `Exactly(n≥2)` (or `AtLeast` /
   `All`), or consumes more than one coloured input, is rejected under EXTENDED — no
   false `Proven` from an over-counted name layer, no dropped base-enabled firing.
3. (MUST) In both BASE and EXTENDED, a net with a reset, read, or inhibitor arc on a
   coloured place is rejected (returns no fragment).
4. (MUST) A declared carrier place not present in the net fails loudly (builder
   rejection or `Unknown` with a reason naming the place); it is never silently
   ignored.
5. (SHOULD) With carriers declared, an end-to-end quiescence property (deadlock-free
   / joined-or-dead-lettered) is decided exactly via Route B — it PROVES on a
   fork-threaded co-mint plus drain fixture and reports VIOLATED when the drain is
   removed, and the verdict is attributable to Route B (the report names the
   name-partition quotient), not the name-blind SMT path.
6. (MAY) A single `Xor` coloured consumer relays the name on one branch and drains
   it on another through the same transition.
7. (MUST) In both BASE and EXTENDED, a matched transition that consumes a coloured
   place through a non-key input is rejected (returns no fragment, no coloured plan),
   and a stranding such a net can reach is not reported `Proven`.
8. (MUST) Under EXTENDED, a coloured consumer whose timeout forwards another input, or
   writes a unit token, into a coloured place is rejected on both routes. With
   `m1: budget → A1`, `m2: budget → A2` minting, `r1: A1, reqA → xor(okA, timeout(20,
   forwardInput(reqA, KA)))`, its twin `r2` into `KB` and a join on `KA`, `KB`, the
   executor reaches `done` when both requests carry one id, and `placeBound(done, 0)` is
   not `Proven`. A consumer whose timeout forwards its coloured input is still a relay.

**Depends on:** [NU-050], [VER-012], [NU-020]
**Test derivation:** `classify` accepts a drain/relay fixture under EXTENDED and
rejects it under BASE; an `Exactly(2)` coloured consumer is rejected (blocker-1 /
blocker-2 regression); a reset-on-coloured net is rejected in both modes; an unknown
carrier name fails loudly; a join consuming another join's key off-key is rejected in
both modes and its reachable stranding is not proven; an end-to-end `deadlockFree` / `JoinedOrDeadLettered`
query on a fork-threaded co-mint plus drain fixture PROVES via Route B and turns
VIOLATED when the drain is removed.

---

#### NU-052: Conflict-Only Priority for the Route B Name-SCG

**Priority:** MAY

The [VER-012] name-aware state-class graph (Route B) is otherwise priority- and
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
  demand is the tokens that transition consumes from `p` on one firing). Read and
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

The default mode, `NONE`, MUST reproduce the prior Route B behaviour byte-for-byte.

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
verifier MUST, whenever it applies `CONFLICT` on a net with a ν-join, split every pruner
`H` (a transition with strictly higher priority than another it shares a consumed input
with) and every transition that deposits into an input or read place of a pruner, and
MUST NOT let `H` pre-empt anything while `inflight:<H>` is marked. When one of those
transitions cannot be split (a ν-join, or a writer into a coloured place, [VER-004]), the
pruning is off for that call: the verdict is the `NONE` verdict and the report names the
transition. The idiom above is such a case, because the join is a pruner and cannot be
split. Under `assumeAtomicFiring` nothing is split and the pruning stays on, and the report
states the atomic assumption. A direct call to Route B (Rust `verify_via_name_scg`,
TypeScript `verifyViaNameScg`) applies no split and prunes as before; the in-flight guard
has no effect on a net without in-flight places.

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

**Depends on:** [VER-012], [NU-050], [NU-020], [VER-004]
**Test derivation:** the minimal ν-join vs. timed dead-letter-drain fixture is
`Violated` under `NONE` and `Proven` under `CONFLICT`; a genuine orphan is `Violated`
under `CONFLICT` without a drain and `Proven` with one; every verdict is attributed
to Route B.

---

#### NU-053: EXTENDED-Coloured Quiescence in the Route A SMT Encoder

**Priority:** MAY

[NU-050] Route A encodes a bounded ν-net as `k` colours and decides
reachability-safety exactly over the **mint → matched-join** fragment. The
solver-free Route B ([VER-012]) additionally decides quiescence and the EXTENDED
coloured-consumer fragment ([NU-051]), but its name-partition graph can blow up on
nets with heavy independent-branch parallelism (no partial-order reduction),
truncating to `Unknown`. An implementation MAY extend Route A's CHC/IC3 encoder so
that it, too, decides quiescence over the EXTENDED fragment — the IC3/PDR engine
does not enumerate interleavings, so it scales where Route B truncates.

Under this extension the coloured encoder:

- admits the EXTENDED fragment ([NU-051]): coloured consumers (relay/drain) and
  declared carrier places, each consuming exactly one coloured input at count one;
- encodes **quiescence** (`DeadlockFree`, `JoinedOrDeadLettered`) as a colour-aware
  deadlock predicate — every transition is disabled for every colour (a mint has no
  globally-fresh colour, a join no shared colour, a consumer no resident colour) and
  the marking is not a sink state. The encoding has no environment-injection rule, so
  it does not answer when injection is modelled ([VER-006] AC7);
- classifies each XOR output branch independently by its own incidence (no 1:1
  net↔flat assumption);
- bounds the simultaneously-live colour count `k` **structurally**, by a linear program over
  the flat net. A colour is live only while some coloured place holds a token of it, so the
  live colours never outnumber the tokens on the coloured places. For any weighting `y` with
  `y ≥ 0`, `y_p ≥ 1` on every coloured place and `y·C_t ≤ 0` for every flat transition `t`
  (the column `post − pre` of [VER-005], a timeout outcome counting its deposit), every
  reachable marking has `Σ_{coloured} M ≤ y·M ≤ y·M0`. This holds with weight on a place a
  reset or consume-all arc clears: at an enabled firing such a place ends at most where its
  column predicts. `k` is `⌊opt⌋`, where `opt` is the least `y·M0` over all such weightings,
  a rational number; equivalently, the largest coloured token count the state equation
  `M = M0 + C·σ` admits over the reals. The optimum is unique, so every implementation
  computes the same `k`. The implementation solves the program itself, in exact rational
  arithmetic, with no solver, and uses its weighting only after an exact re-check in
  arbitrary-precision arithmetic (`y ≥ 0`, `y_p ≥ 1` on every coloured place, `y·C_t ≤ 0` on
  every flat transition, `k = ⌊y·M0⌋`). A weighting that fails the re-check is discarded and
  the plan is refused; it never sets `k`. When no weighting exists (the program is
  infeasible) the coloured tokens are not structurally bounded, a genuine colour leak, so the
  plan is refused and the query falls back to the sound over-approximation. `k = 0` is a
  bound like any other: with fewer than one coloured token possible, no mint, join or
  coloured consumer can ever fire (Lean `vacuous_colour_layer_lp`), and the zero-slot plan is
  exact rather than a fallback. A budget place that gates minting yields such a weighting, a
  refund to a non-minting place leaves the minting budget covering, and a leaky co-mint
  fan-out (a colour co-minted into a place no matched join re-collects) admits none and falls
  back rather than certifying a false `Proven`. A relay threads its colour onward and still
  MUST NOT refund: the freed budget could mint a `(k+1)`-th live colour.

The update of a coloured consumer, per colour `c`, emits `(- x 1)` for its input column
and `(+ x 1)` for each coloured output column. A consumer that relays into its own
input (a self-loop, `spin: a, tick → a, tock` with `a` coloured) gets **no** update term
for that column: it keeps its `>= 1` guard and is carried over unchanged, as a join's
key that is also a relay target is ([NU-054]). A rule updates each column once, so
emitting both terms would keep only the `(+ x 1)` and leave the consumer unable to fire
under any law that weights `a`.

The verifier routes a bounded quiescence query to Route B first; when Route B
truncates (`Unknown`), it **defers** to this scalable Route A encoding rather
than returning `Unknown`. A verdict from the coloured plan is not downgraded
(the colour-aware deadlock does not over-fire joins). Its `Proven` is sound while the
declared mints and the coloured consumers keep their contracts ([NU-010], [NU-051]);
the report prints the colour-slot bound as `colour-slot bound k=<k>`, after the line
`Colour-slot bound: LP optimum <opt> over <n> places and <m> transitions, so k=<k>
(re-checked in exact arithmetic)`, and names the transitions whose contracts it assumes.
When the program yields no bound the line reads `Colour-slot bound: none (<reason>)` and
no plan is built.

For a reachability-safety property the linear state-equation bound of [VER-015] runs
before the coloured query (after Route B). The bound is written over the flat,
name-blind net, which over-approximates the ν semantics, so its `Proven` (method
`structural`) is sound here and ends the query; any other outcome hands over to the
coloured query unchanged. The colour-slot bound `k` is often several times the budget,
and a trivially true bound that IC3 cannot close over `k` colours within the timeout
is proven by the state equation in milliseconds. The coloured plan, and the linear program
behind its slot bound, are built only when the bound does not prove.

**Acceptance criteria (MAY):**
1. A budget-bounded EXTENDED ν-net whose only quiescent marking holds sink tokens is
   `Proven` deadlock-free via the coloured Route A encoding.
2. Removing the drain (or otherwise making a correlation name strand) turns the same
   query `Violated`.
3. Route A and Route B agree on every small fixture both can decide (differential
   soundness).
4. A net whose coloured set has **no covering weighting** (the slot-bound program is
   infeasible) — an
   unbounded colour leak, e.g. an over-refund that inflates the *minting* budget, or
   a relay that refunds and frees a token for a `(k+1)`-th colour — falls back to the
   sound over-approximation rather than a false `Proven`. (A refund to a *non-minting*
   place keeps the minting budget a covering weighting, so it stays bounded and is
   admitted — the structural bound is more precise than the old budget-conservation
   heuristic.)
5. A leaky co-mint fan-out — a fork co-minting one colour into a place the refunding
   join never re-collects (e.g. an un-drained carrier) — falls back rather than a
   false `Proven`: the colour would otherwise outlive its budget and the k-colour
   encoding would under-approximate.
6. A slot-bound optimum below one (a mid-phase marking with no budget token, or a mint that
   needs more budget tokens than the marking can ever supply) yields the exact plan with
   `k = 0`: quiescence is decided, never downgraded to `Unknown`, and the emitted encoding is
   well-formed with zero colour slots. The plan is still refused when the program is
   infeasible.
7. Under EXTENDED, `mint: budget → a, b` (one fresh name), `spin: a, tick → a, tock` and a
   join on `a`, `b`, from `{budget, tick}`: `placeBound(tock, 0)` is `Violated` through
   the coloured encoding, since `spin` can fire.
8. `k` is the floor of the slot-bound program's optimum, identical in every implementation,
   and never larger than the bound of any covering non-negative P-semiflow. On the
   scatter-gather net (`source` 3 and `budget` 2 tokens, a fork consuming one of each and
   co-minting into `branchA`, `branchB` and `pending`, a join on `branchA`, `branchB`
   refunding `budget`) `k = 4`, where the semiflow bound was 10. With a fork that consumes
   `exactly(3)` budget tokens into the two keys, a join that refunds one, and a budget of 7,
   the optimum is `14/3` and `k = 4`. `encodeScripts()` emits that `k` without starting a
   solver ([VER-013] AC1).
9. A weighting is used only after the exact re-check: one that is negative somewhere, below
   one on a coloured place, or increasing along a flat transition refuses the plan with the
   report line `Colour-slot bound: none (LP weighting failed the exact re-check: <reason>)`.
   A reset or consume-all arc on an uncoloured place does not refuse the plan by itself:
   `mint: budget → a, b`, `join: a, b → budget` keyed on `a` and `b`, and `cancel: r → r2`
   with a reset arc on `budget`, from `{budget: 2, r: 1}`, has `k = 4`.

**Depends on:** [NU-050], [NU-051], [VER-004], [VER-005], [VER-006], [VER-012], [VER-013], [VER-015]
**Test derivation:** a co-mint→join net is `Proven` deadlock-free via Route A when
Route B is forced to truncate; an EXTENDED drain-steal net is `Violated`; the two
routes agree on the no-stall net. The scatter-gather net has `k = 4`; the `exactly(3)` fork
from one budget token has `k = 0`; a reset arc on the uncoloured budget keeps the plan.

---

#### NU-054: Join Relay

**Priority:** MAY

A matched join ([NU-020]) consumes a name and, in the analysed fragment, may not write a name
onto a coloured place: the analyzers read any coloured output of a join as a re-mint and reject the
net to the over-approximation. That blocks two shapes that are routine in object-centric models: a
**join chain**, whose join hands the matched name on to a later join (`e: C1, D1 → P5` followed by
`f: P5, OR → R`), and a **correlated self-loop**, whose join writes the matched name back onto one
of its own keys (`B: p, Y1 → Y1, w, q`). Five of the eleven ν transcriptions of the PNID figures
in `research/net-metrics/validation/pnid/` fall back for this reason alone, and every quiescence
property on them comes back `Unknown`.

**Declaration.** A match specification MAY declare **relay targets**: output places onto which the
join writes the name it matched, each with a `value → NameId` key projection like a match key's.
Every relay target MUST appear in the transition's output spec (in at least one branch), and a
place MUST NOT be declared twice; either violation is rejected when the transition is built, naming
the transition and the place. A relay target MAY also be one of the join's own match keys (the
self-loop). Under composition the relay targets are remapped by the same place rewrite as the keys
([NU-030], [NU-060]). A rewrite that maps two relay targets of one join onto one place (fusion or
port binding) produces a relay target declared twice and is rejected at rebuild with the same
error, as the other collisions of [MOD-020] are.

**Runtime contract, checked.** A firing of the join MUST write, into each relay target of the branch
it produced, only tokens whose key projects to the matched name. The executor checks this on every
firing, as part of output validation ([IO-015]): a token in a relay target whose projection is a
different name, or no name, fails the firing like any other validation failure. A token whose
value is absent (`null` / `undefined` / `None`, such as the unit token of an `Out.place` in a
timeout branch) has no name: the check reports it as such **without** calling the projection. It
fails the firing like any other validation failure, with an error
naming the transition, the place, the matched name and the name found. A projection that
**fails** (throws, or raises) yields no name either: the firing fails with the same "no name"
error, whatever the failure was. Rust projections are infallible by type (`Fn(&T) -> NameId`), so
there is nothing to catch; a projection that panics propagates like a panic in the action, and no
implementation wraps it in `catch_unwind`. The relay check runs **before** the multiplicity
diagnostic of [IO-016] AC4, in both executor backends of every language, so a firing that both
violates the relay contract and over-writes a place fails with the relay error and emits no
multiplicity `WARN`. In Rust, a relay violation found while flushing a mid-action batch
([IO-015]) makes `ctx.flush()` return `Err` carrying the relay message, rather than recording it
and returning `Ok`; the firing then fails as it does for a violation found at completion. The
check is on by default
and is skipped only where output validation itself is skipped ([CONC-026]). Every token the firing
deposits in a relay target is checked, whatever wrote it, including an `Out.forwardInput` or
`Out.timeout` branch ([IO-013], [IO-014]); a batch published mid-action ([IO-015]) is checked when
it is published. The check is what distinguishes this requirement from the relay of [NU-051],
whose contract is only documented: here the analysis's reading of the transition is enforced
against what the action does.

**Name layer ([VER-012], Route B).** Under the EXTENDED fragment ([NU-051]) the relay targets of
every join are unioned into the coloured set, as declared carrier places are, **before** the fragment
rules below are checked, so the off-key and read/inhibitor/reset rules apply to relay targets as
to any coloured place. A relay target no join consumes is still coloured: its consumers take the
[NU-051] consume role and any other producer the mint role, when it is a declared mint
([NU-010]). A join firing on
symbol `s` removes `s` from its keys as before, then adds `s` **once** to each relay target in the
fired branch. A branch with no relay target drains `s`, as a join does today; an `Xor` join may
relay on one branch and drain on another. The step mints nothing, so the live-name pool does not
grow: the quotient is finite whenever it was finite with the relay replaced by a drain. The
canonical key format is unchanged, so byte parity across languages holds. The step commutes with
renaming (it adds the symbol it removed), so the per-role equivariance that Lean `Interning.lean`
assumes for `Join` covers the relay role by the same argument, and the orbit dedup of [VER-012]
still applies: two enabling symbols with equal signatures still yield successors with equal keys.

**Coloured IC3 ([NU-053], Route A).** The per-colour expansion of a join additionally produces
colour `c` on each relay target of the fired branch. The encoding stays in linear arithmetic, and
the colour-slot bound is unchanged in kind: the relay targets are coloured places, so the covering
non-negative P-semiflow that bounds `k` MUST weight them too, and a net with no such semiflow falls
back as it does today.

The update of a relaying join, per colour `c`, is fixed so the scripts stay byte-identical across
languages ([VER-013]): the guards are unchanged (each key column `>= 1`); the update emits
`(- x 1)` for each key column that is not also a relay target, then `(+ x 1)` for each relay-target
column that is not also a key. A column that is **both** a key and a relay target (a correlated
self-loop) gets **no** update term: it keeps its `>= 1` guard and is carried over unchanged. A
coloured output of a join that is not a relay target, or a relay target produced with a count
other than one, is outside the fragment (see the rules below).

**Fragment rules.** Relay targets change the classification only under EXTENDED. The analyzer
still rejects, falling back to the sound over-approximation with an "EXTENDED declined" note:

- a join that produces a coloured place it does not declare as a relay target (a re-mint, as
  before);
- a relay target that the same join also consumes through an input that is **not** one of its
  match keys (the off-key rule of [NU-051] AC7, which the relay target meets once it is coloured);
- a relay target carrying a read, inhibitor or reset arc on any transition (the exclusion of
  [NU-051], for the same reason);
- a join whose `Timeout` branch writes a relay target by anything other than a forward of one of
  its match keys. The runtime check above covers timeout deposits too: an `Out.place` leaf writes a
  unit token with no name, and a forward of another input carries that input's name, so that
  firing fails and deposits nothing. The name layer would relay the matched name instead, and a
  later join could then fire in the graph but not at run time. A forward of a match key carries
  the matched name and is admitted. This is the same rule the coloured consumer of [NU-051] and
  the declared mint of [NU-010] follow for their timeout writes.

Under **BASE** the relay declarations are ignored by the analyzer, as declared carriers are: the
coloured set is the match keys alone, and a join producing one is rejected as it is today. BASE is
defined as the shipped mint → matched-join fragment, reproduced exactly; the relay is a coloured
role like the drain/relay consumer, and one knob selecting every coloured role keeps both modes'
meaning plain. A verifier that meets a relay declaration under BASE SHOULD say in its report that
the declaration was ignored and name EXTENDED. The runtime check is independent of the mode.

**Acceptance Criteria:**
1. (MUST, where offered) A relay target that is not an output of the transition, or is declared
   twice, is rejected at transition build with an error naming the transition and the place.
2. (MUST, where offered) At run time, a join whose action writes into a relay target a token
   projecting to a name other than the matched one, or to no name, fails that firing with a
   validation error naming the transition, the place and both names; the same net with a
   conforming action fires normally. Both executor backends in every language agree. A key
   projection that throws fails the firing with the "no name" error, and a firing that also
   over-writes a place emits no [IO-016] AC4 `WARN`: the relay check runs first.
3. (MUST) Under EXTENDED, the join chain `fork: S → A, B, D` (mint), `j1: A, B → C` relaying to
   `C`, `j2: C, D → done` decides `unreachable(done)` (`Violated`) and `deadlockFree` with `done` a
   sink (`Proven`) through Route B rather than falling back. A variant in which `D` is filled by a
   second, independent mint reports `done` unreachable: no two different names are equated.
4. (MUST) Under EXTENDED, a join that produces a coloured place not declared as a relay target,
   or that consumes its relay target through a non-key input, is rejected (no fragment), as is a
   relay target with a read, inhibitor or reset arc. So is a join whose timeout writes a relay
   target as a unit token or as a forward of a non-key input: on the AC3 chain with `j1`'s output
   `xor(C, timeout(C))`, `deadlockFree` is not `Proven`, and neither Route B nor Route A decides
   it. The same chain with `timeout(forwardInput(A, C))` is still `Proven` through Route B.
5. (MUST) Under BASE, a net whose only change is a relay declaration gets the verdict it got
   without one, and the report names the ignored declaration.
6. (SHOULD) Route A ([NU-053]) and Route B agree on every small relay fixture both decide.
7. (MUST) No canonical name-partition key changes for a net without relay declarations: the
   cross-language key fixtures are byte-identical before and after.

**Test derivation.** PNID fixtures from `research/net-metrics/validation/pnid/src/nets.ts`, each run
under EXTENDED with its declared budget and carriers, before and after declaring the relays:

- **Fig. 12(c)** (closure 2): `e: C1, D1 → P5` relays to `P5`, a key of the `f`/`g` joins. Today
  `deadlockFree` is `Unknown` (EXTENDED declined); with the relay both `deadlockFree` (sink `R`)
  and `placeBound(OR, 2)` are decided at k = 1 and 2 — by Route B, or for `placeBound` by Route A
  when a budget is declared (budgeted reachability-safety routes there per [NU-053]) — and agree with the paper's label
  (both hold). A disagreement is reported, not tuned away.
- **Fig. 6(a) N1, correlated**: `B` relays to `Y1` (its own key), `w` and `q`; `D` relays to `Y2`
  (its own key) and `r`. `deadlockFree` is decided by Route B: `Violated` with the trace `A, C`,
  the name-blind control's witness (C moves the case's `Y1` token before `B` can join on it, and
  the `p` token strands).
- **S union N ⊕ M**: `b: p, s → q` relays to `q`. `deadlockFree` is `Violated` with the trace `a`
  (b waits for an `s` that only `c` produces, after `b`), now reached through Route B for the
  right reason rather than by reading `c` as a mint.

Plus AC1 and AC2 at build and run time in every executor, AC4's rejections through `classify`,
AC5 on Fig. 12(c) under BASE, and the existing key fixtures for AC7.

**Implementation notes (API):** the relay is declared on the match specification, beside its keys.

- Java: `MatchSpec.builder().key(C1, fn).key(D1, fn).relayTo(P5, fn).build()`; `MatchSpec.relays()`
  lists them as `MatchKey`s; `remap` maps them with the keys.
- TypeScript: `matchSpec(matchKey(C1, fn), matchKey(D1, fn), relayKey(P5, fn))`; a `relayKey` is
  told apart from a `matchKey` and does not count towards the two correlated inputs;
  `MatchSpec.relays`.
- Rust: `MatchSpec::builder().key(&c1, f).key(&d1, f).relay_to(&p5, f).build()`;
  `MatchSpec::relays()`.
- Python: `match_spec(keys=[(c1, fn), (d1, fn)], relay_to=[(p5, fn)])`; the projection is a Python
  callable, evaluated under the GIL like a key.
- Export MAY decorate a relay edge like a match input ([EXP-018]); nothing requires it.

**Fixtures.** The relay nets used for the cross-language script parity ([VER-013] AC1) live in
`spec/verification-fixtures/nu-relay-fixtures.json`, given inline as rows (transition, inputs,
outputs, match keys, relay targets) with their marking, carrier places, fragment mode and expected
verdict; their goldens are `spec/verification-fixtures/scripts/nu-relay-*/`, written by the Rust
script-parity test and never by hand.

**Results on the PNID figures** (all four implementations agree): Fig. 12(c) `deadlockFree` and
`placeBound(OR, 2)` are `Proven` (were `Unknown`); S union N ⊕ M is `Violated` with the trace `a`;
Fig. 6(a) N1 correlated is `Violated` with the trace `A, C`, which disagrees with the paper's
"identifier sound" label and is reported as such, not tuned. Route A agrees with Route B wherever
it decides; on the proven quiescence cases it returns `Unknown` (Spacer).

**Depends on:** [NU-020], [NU-030], [NU-051], [NU-053], [VER-012], [IO-015], [IO-016], [CONC-026]

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
- The [NU-050] carve-out (**Route A: bounded name-colouring**) is
  implemented for the **mint → matched-join fragment** of a budget-declared
  ν-net: there, reachability-safety properties are decided over `k` colour slots,
  with no counterexample that equates two different names, so neither `Proven` nor
  `Violated` carries the over-approximation caveat. The verdict rests on the mint and
  relay contracts ([NU-010], [NU-051]). A
  budget-declared ν-net **outside** that fragment falls back to the sound
  over-approximation: a reachability-safety `Proven` is sound (the real net fires
  strictly fewer joins) and a `Violated` is flagged as possibly spurious pending
  the fuller [NU-050] analysis.
- The [NU-050] **Route B** exact analysis (the **SCG name-partition quotient**) is
  implemented in all four bindings (Rust is the source of truth; Python inherits
  it through `verify`; Java and TypeScript port it byte-faithfully, sharing the
  canonical name-partition key format). It decides reachability-safety **and**
  quiescence over the mint → matched-join fragment **without requiring a declared
  budget** for finiteness (that comes from the name-permutation symmetry quotient;
  the mints are still declared, [NU-010]), and
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
