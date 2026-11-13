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
**Kind:** F

A **name** (`NameId`) is an opaque correlation identity, constructed from an
underlying string value. Whether a matched transition is enabled, and which tokens
its firing consumes, *shall* depend on the names its keys project only through name
**equality** and, for the tie-break of [NU-020], the name order. The name order
exists solely for that tie-break and carries no domain meaning.

*When* a matched transition fires with a chosen name, and a one-to-one renaming of
names makes the renamed chosen name the chosen name ([NU-020], [NU-022]) of the same
transition with every name its keys and relay targets project renamed, at the same
marking, that renamed transition *shall* fire from that marking with the renamed
chosen name, for the same emission, delivering the same tokens and leaving the same
marking.

The name constructor *shall* return equal names for equal underlying values and
different names for different underlying values. Each implementation *shall* order
names by one fixed strict total order, the name order: if one name precedes another,
the other does not precede it; if a first name precedes a second and the second
precedes a third, the first precedes the third; and of two different names, one
precedes the other. Of two names whose underlying values hold only Basic
Multilingual Plane characters, one *shall* precede the other exactly when its value
precedes the other's in the lexicographic order of code points. On other names the
name order need not agree across implementations: Rust and Python order by code
point, Java and TypeScript by UTF-16 code unit, and the two orders disagree on some
names that hold supplementary-plane characters ([NU-020]).

Identity is a **projection of the token payload**, not a field on the token: a
[NU-020] match (or the analyzer) declares a `value → NameId` key. The token model
([CORE-010]) is unchanged: no name field is added, so event ([EVT-011],
[EVT-012]) and archive formats are unaffected.

**Acceptance Criteria:**
1. Two names constructed from the same underlying value are equal; from
   different values, unequal.
2. Names admit a stable total order consistent across a single implementation.
3. Adding ν-matching to a net does not change the token type or the on-the-wire
   shape of token-bearing events.
4. A one-to-one renaming of the names a join's keys project, which makes the
   renamed chosen name the chosen name of the renamed join, does not change which
   tokens the join consumes or the marking it leaves.

**Test derivation:** Construct `NameId("a")` twice; verify equal. Verify
`NameId("a") < NameId("b")`. Verify a net with no match spec emits identical
token events with and without the ν-net APIs linked. Run a two-branch join on a
marking where two names can join and their earliest tokens differ, then the same
join with its keys composed with a swap of the two names; verify that the renamed
join fires with the renamed name, consumes the same tokens and leaves the same
marking.

---

## ν-binder (Fork)

#### NU-010: Fresh-Name Minting

**Priority:** MUST
**Kind:** B

A transition action MAY mint a fresh name via the action context
(`ctx.freshName()` / `ctx.fresh_name()`). The action writes the minted name into
the payloads it produces, so the sibling tokens of a fork (an [IO-011] AND
output) share one correlation name.

Minted names MUST be unique across all firings of a single execution and MUST be
deterministic for a fixed scope ([NU-011]) and a fixed sequence of calling transitions (replay
stability). So the names follow the order of the `freshName()` calls, not the order of the
firings: with one minting action in flight at a time the two orders agree, and actions that run
concurrently may call the minter in either order. The executor installs the minter, one counter
shared by all its transitions ([NU-011]); absent an executor-installed minter, a fallback still
guarantees uniqueness.

*When* an action calls `freshName()`, the executor *shall* return a name that differs from every name it returned earlier in the same execution, whether the earlier call came in the same firing or in an earlier one.

For a fixed scope and a fixed sequence of calling transitions, the executor *shall* return the same sequence of names to the `freshName()` calls, whichever firings the calls fall in.

What replays is the sequence **within a minting scope** ([NU-011]). Under the
default scope the scope component of a name differs from run to run by design
(that is what keeps a resumed execution from re-minting a live name), so a host
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

Every name a declared mint writes into a coloured place ([NU-051], [NU-054]) it writes
without consuming one MUST be a name it minted with `freshName()` in that firing, and all such
names MUST be one and the same, whether in one place or in several. A transition
that writes a coloured place without consuming one and is not declared keeps the net off
both routes, and the verifier answers through the name-blind over-approximation. What
the executor writes on timeout ([IO-013], [IO-014]) is never a mint, declared or not: a
`ForwardInput` copies a consumed token, name included, and an `Out.Place` writes a unit
token, which has no name. A declared mint that is not a transition of the net MUST be refused, by a
failure or an `Unknown`, with the same reason naming it at every entry point (verification, script encoding
([VER-013]) and open-net verification ([VER-022])): `declared mint transition 'x' not in the
net (NU-010)`, or `declared mint transitions 'a', 'b' not in the net (NU-010)` when several
are not, each named once in code-point order. A refusal that does not depend on the
declaration, such as a stop before the call starts ([VER-013]) or an unresolved property
place ([VER-003]), may come first, and that refusal is then the answer. Java throws where the mint is declared, the open-net hook
included. TypeScript throws where it is declared on a verifier, and open-net verification
answers `Unknown`. Rust answers `Unknown` from verification and open-net verification before
any route runs, and its script encoding panics; Python raises `ValueError` from script
encoding. The report
of a verdict from either route names the transitions whose mint contract it assumes. When
Route B declines a net only because a transition writes a coloured place without consuming
one and is not declared, the report names that transition and points at the declaration.

*When* a declared mint that has no input arc on a coloured place fires, every name it writes into a coloured place *shall* be a name it minted with `freshName()` in that firing.

*When* a declared mint that has no input arc on a coloured place fires, every name it writes into coloured places *shall* be one and the same name, whether in one place or in several.

The fragment classifier ([NU-051]) *shall* give the mint role only to a declared mint.

*If* a transition without a match specification has no input arc on a coloured place, writes a coloured place and is not a declared mint, *then* the fragment classifier *shall* give it no role.

*If* the timeout outcome of a transition writes a coloured place, *then* the fragment classifier *shall not* give it the mint role.

*If* a transition without a match specification has no input arc on a coloured place and its timeout outcome writes a coloured place, *then* the fragment classifier *shall* give it no role.

The fragment classifier *shall not* give the mint role to a transition that has a match specification or an input arc on a coloured place.

*If* a declared mint has no match specification, no input arc on a coloured place and no reset, read or inhibitor arc on a coloured place, puts on each branch exactly one token, and never a drained batch, into each coloured place the branch writes, writes a coloured place in some outcome and on timeout writes no coloured place, *then* the fragment classifier *shall* give it the mint role, in both BASE and EXTENDED.

*If* a name given to the verifier as a mint transition is not a transition of the net, *then* verification, script encoding and open-net verification *shall* each refuse the request, by failing or by answering `Unknown`, and *shall not* answer `Proven` or `Violated` or return scripts.

*If* a name given to the verifier as a mint transition is not a transition of the net, *then* the reason of that refusal *shall* be `declared mint transition 'x' not in the net (NU-010)`, or `declared mint transitions 'a', 'b' not in the net (NU-010)` when several are not, naming each such name once and in code-point order, unless the same request with no mint transition named gets the same refusal.

*If* every name given to the verifier as a mint transition is a transition of the net, *then* verification, script encoding and open-net verification *shall not* refuse the request with the reason `declared mint transition 'x' not in the net (NU-010)` or `declared mint transitions 'a', 'b' not in the net (NU-010)`, whatever names it gives, unless the same request with no mint transition named gets the same refusal.

**Acceptance Criteria:**
1. Two `freshName()` calls, within one firing or across firings, return
   unequal names.
2. A fork that stamps both AND-branches with one minted name produces sibling
   tokens that a [NU-020] join later correlates.
3. For a fixed sequence of calling transitions and a fixed scope ([NU-011]), the sequence of
   minted names is reproducible.
4. (MUST, where the [NU-050] routes are offered) `mA: S1 → A` and `mB: S2 → B` with the stock `fork()`, and a join on `A`, `B` into
   `DONE`: with one correlation id in `S1` and `S2` the executor reaches `DONE = 1`, and
   `placeBound(DONE, 0)` is not `Proven` unless `mA` and `mB` are declared mints. Declared,
   it is `Proven` by Route B and the report names `mA, mB` under the mint contract.
5. (MUST, where offered) `t1: budget, reqA → xor(okA, timeout(20, forwardInput(reqA, a)))`, its twin `t2` into
   `b`, and a join on `a`, `b`: the executor forwards both requests on timeout and joins
   them when they carry one id. `placeBound(done, 0)` is not `Proven` on either route,
   with `t1` and `t2` declared or with `budget` a declared budget place.
6. (MUST, where offered) A name given to the verifier as a mint transition that is not a
   transition of the net is refused, by a failure or an `Unknown`, with a reason naming it,
   unless a refusal that does not depend on the declaration is the answer; a name that is a
   transition of the net is not refused with that reason.

**Depends on:** [CORE-050], [IO-011], [IO-013], [IO-014], [NU-040], [NU-050]
**Test derivation:** A `fork` transition mints a name per firing and stamps both
output branches; with three source tokens, verify three distinct names reach the
downstream join and each pair merges (see `nu_fork_mints_unique_ids_then_join_merges`).

---

#### NU-011: Resume-Safe Fresh-Name Minting

**Priority:** MUST
**Kind:** F

[NU-010] scopes minted-name uniqueness to "a single execution". Restoring a marking
([CORE-073]) begins a **new** execution whose initial marking already holds names minted by
the previous one. An implementation that satisfies [NU-010] by counting firings from zero
therefore re-mints names that are already live — and because a [NU-020] join correlates on
name equality alone, the collision does not surface as an error: it silently correlates
tokens from different run segments, merging a restored token with an unrelated fresh one.

Names minted by an execution seeded from a restored marking MUST NOT collide with names
minted by any other execution in the same restore lineage, other than a replay of the same
segment (AC3), whether or not those names are still present in that marking. The mechanism is not prescribed. Two that satisfy it:

- a per-execution **scope** supplied by the host and incorporated into every minted name;
- carrying the minter's high-water mark in the snapshot and resuming strictly above it.

Under the scope mechanism, names minted under two different accepted scopes never collide, so
the guarantee rests on the executions of a lineage running under different scopes: the default
scope is drawn at random per executor (below), and a pinned scope is the host's promise. A
replay that re-runs a segment under its pinned scope, from the marking the segment started from
and with the same `freshName()` calls, mints the segment's names again, which is AC3, not a
collision between segments. A name the host writes into a token itself, such as a copied
correlation id, is not a minted name and is not covered.

**The restore lineage crosses processes.** [CORE-073] offers restore as a suspend boundary, a
durable checkpoint, a crash-recovery point — so the execution that resumes a marking is, in the
normal case, running in a *different process* from the one that minted the names in it. "Unique
per executor" read as "unique within a process" is therefore not enough. Anything derived from a
per-process counter restarts with the process, and the first executor of the new process re-mints
the first name of the old one: exactly the silent merge above, in the default configuration.

**The default scope MUST be unique across processes — and is therefore not the run identifier.**
Absent a host-supplied scope, an implementation using the scope mechanism MUST
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
a fixed restored high-water mark) and a fixed order of `freshName()` calls, the minted
sequence MUST be reproducible. The firing order fixes the order of the calls when at most one
minting action is in flight at a time, or when every call is made inline by a synchronous
action. Randomness is therefore admitted in exactly **one** place — the *default* scope,
chosen once per executor — and nowhere else: the counter `<n>` MUST NOT be random, and a scope
the host pinned MUST be used verbatim, with nothing random mixed into it or into the sequence
minted under it. A host that needs a reproducible segment pins its scope (AC3). A host that pins
nothing gets uniqueness instead of reproducibility, and that is the right default: an
unreproducible name is visible and harmless, a cross-segment merge is neither.

*If* a host-supplied scope is empty or contains `:` or `#`, *then* the executor *shall* reject it when it is configured.

The executor *shall* accept a host-supplied scope that is not empty and contains neither `:` nor `#`, a whitespace-only scope included.

*Where* an executor uses the scope mechanism, the `i`-th `freshName()` call it answers, counting from zero across all its firings and transitions, *shall* return `<t>#<s>:<i>` with `i` written in decimal, where `t` is the name of the calling transition and `s` is the executor's scope, verbatim as the host pinned it or as it was drawn by default.

*Where* executors use the scope mechanism, no name minted by an execution under one accepted scope *shall* equal a name minted by an execution under a different accepted scope.

*Where* an executor is given no scope, the executor *shall* draw its scope from the platform's random source as 32 lowercase hexadecimal characters, which neither its construction order nor its run identifier determines.

A host *shall not* pin one scope for two executions of one restore lineage, except for a replay: an execution that re-runs an earlier segment, after it and not alongside it, from the marking that segment started from and with the same `freshName()` calls.

**Acceptance Criteria:**
1. Restore a marking holding a name `n` minted by a prior execution; run the resumed
   execution, under the default scope or a pinned scope other than the prior execution's, so
   it mints at least as many names as the original minted; no minted name equals `n`.
2. A restored token awaiting its sibling at a [NU-020] join is not correlated with a
   freshly minted token of the resumed segment.
3. For a fixed scope and a fixed order of `freshName()` calls, two runs from the same restored
   marking mint the identical name sequence.
4. Two concurrent executions restored from the same snapshot, under the default scope or under
   two different pinned scopes, mint disjoint name sets.
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
**Kind:** B

A transition MAY declare a **match specification**: a subset of its **input**
places, each with a key projection from a token's value to a `NameId` or to no name. Every
place named by the match MUST also be a declared input. The match adds a correlation
requirement on top of the existing input cardinalities ([IO-001]–[IO-004]):

- **Enablement** = the usual cardinality/bitmap/inhibitor checks ([CORE-022])
  **and** there exists a single name `n` present in *every* correlated input
  with at least that input's required count of key-projecting-to-`n` tokens.
- **Firing** consumes, for the chosen `n`, the matched tokens from each
  correlated input (FIFO within a name); non-correlated inputs consume FIFO as
  usual ([EXEC-010]).

A key projection may yield no name for a token (a value of another type, a projection that
returns no value): such a token has no name on that input, so that input never matches it and
never consumes it.

A match names each correlated input once: the input's cardinality, not a repeated key, sets how
many tokens of the name it takes. Building a match or a transition whose match keys one place
twice MUST fail. A match builder given fewer than two keys MUST fail; a construction path that is
not a match builder (Rust `MatchSpec::from_keys`, a TypeScript object literal) leaves that minimum
to the caller. Every correlated input requires at least one token ([IO-002], [IO-004]).

**Build.** The match checks run after every other build-time check of the transition: a place
keyed twice, then a key on a place that is not an input place, then the relay checks of
[NU-054]. The first check that fails names the error.

*If* a match builder is given fewer than two keys, *then* building the match *shall* fail.

*If* a match specification keys one place twice, *then* building the match *shall* fail.

Building a match from two or more keys on distinct places *shall* succeed.

*If* a transition fails to build without its match specification, *then* building it with the match specification *shall* fail.

*If* the match specification of a transition keys one place twice, *then* building the transition *shall* fail.

*If* the match specification of a transition keys a place that is not an input place of the transition, *then* building the transition *shall* fail.

Building a transition with a match specification *shall* succeed when the transition builds without the match, the match keys distinct input places of the transition, and the match declares each relay target once and as an output place of the transition ([NU-054]).

**Enablement and the chosen name.**

*When* a transition with a match specification fires, it *shall* be enabled on its token counts ([CORE-022]).

*When* a transition with a match specification fires, every correlated input *shall* hold at least one token of the chosen name and at least its required count of tokens of that name.

*When* a transition with a match specification fires, no other name of which every correlated input holds at least its required count of tokens *shall* have an earlier earliest `createdAt` among its tokens in the correlated inputs than the chosen name, or the same and precede it in the name order.

**Firing.**

*When* a transition with a match specification fires, its action *shall* receive from each correlated input the first tokens of the chosen name in queue order, as many as the consumption count of the input arc with `available` the number of tokens of the chosen name in the place ([IO-007]).

*When* a transition with a match specification fires, each correlated input that is not one of its reset places *shall* end the firing holding the tokens it did not deliver, in their order, followed by the tokens the firing deposited there.

*When* a transition with a match specification fires, its deposit *shall* be one its output spec offers for the tokens the firing takes ([IO-013], [IO-015]).

*When* a transition with a match specification fires, its read arcs *shall* deliver the head of each read place after the inputs are taken ([EXEC-012]).

*When* a transition with a match specification fires, each of its reset places *shall* end the firing holding only the tokens the firing deposited there ([CORE-034]).

*When* a transition with a match specification fires, each place that is not a correlated input *shall* deliver to its action, and keep, the tokens it would without the match specification: the tokens at the head of its queue, as many as the consumption count of its input arc and none without one, and, unless it is a reset place, the rest of its queue in order followed by the tokens the firing deposited there ([EXEC-010], [EXEC-020]).

**Determinism (tie-break).** When more than one name satisfies the join, the
implementation MUST choose by this exact rule, so all languages fire identically on names whose
values hold only Basic Multilingual Plane characters ([NU-001]):
1. the name whose earliest `createdAt` among all tokens carrying the name in the correlated
   inputs is **earliest**, whether the firing consumes those tokens or not;
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
4. The tie-break selects the name with the earliest `createdAt` among its tokens in the
   correlated inputs, then the least name in the name order; implementations agree on names of
   Basic Multilingual Plane characters ([NU-001]).
5. A match that keys one place twice is rejected when the match is built, and when a
   transition is built with such a match from any other construction path (a bindings layer,
   a composition remap, an object literal).

**Depends on:** [IO-001], [IO-002], [IO-003], [IO-004], [IO-005], [IO-007], [CORE-022], [CORE-013], [EXEC-010], [NU-001], [NU-022]
**Test derivation:** `nu_join_matches_by_name_not_fifo` (reversed arrival),
`nu_join_blocks_without_matching_name`, mirrored across every executor in every
language.

---

#### NU-021: Match as the Sole Per-Token Filter

**Priority:** MUST
**Kind:** B

Name correlation ([NU-020]) is the **only** per-token filter the enablement check
applies. There is no unary value predicate on an input: guards were removed in
[IO-006] and no implementation carries one, so token selection is determined by
position ([EXEC-010], [IO-007]) and, on correlated inputs, by name equality, with the
chosen name picked by the tie-break of [NU-020], which reads names and `createdAt` only.
Nothing else about a token's value is read.

A pairing of values says, for each place, which pairs of values may stand in for each other
there. A transition's keys and relay targets cannot tell a pairing apart when every key on a
place, and every relay target at a place, projects the two values of each pair on that place to
the same name or to no name. On a place that no key and no relay target reads, a pairing may
pair any two values, and a transition without a match specification has no keys, so for it any
pairing qualifies. Two markings differ by a pairing when every place holds as many tokens in
both and the tokens at the same queue position of a place have the same `createdAt` and values
the pairing pairs on that place. Two emissions, or two deliveries, differ by a pairing when they
hold such tokens on the same places in the same order.

*When* a transition fires, it *shall* also fire with the same chosen name from every marking that differs from its marking only by a pairing its keys and relay targets cannot tell apart, for every emission that differs from its emission by the same pairing, delivering tokens and leaving a marking that differ from its own by the same pairing.

*When* a transition with a match specification fires, every token it delivers from a correlated input *shall* project to the chosen name under that input's key.

*When* a transition with a match specification fires, each correlated input that is not one of its reset places *shall* end the firing holding, of the tokens that do not project to the chosen name, exactly the ones it held before, in their order, followed by the ones the firing deposited there, in the order deposited.

*Note (non-normative).* Should a future revision reintroduce a unary input filter, the
intended composition order is: the filter applies **first** and the name correlation runs
over the survivors, so a token must pass the filter *and* project to the chosen name to be
consumed. No implementation has such a filter today.

**Acceptance Criteria:**
1. No input specification variant exposes a value predicate; the enablement check
   evaluates no per-token predicate other than name equality on correlated inputs.
2. A correlated input consumes only tokens carrying the chosen name; a same-place
   token of a different name is left behind regardless of its value.

**Depends on:** [NU-020], [EXEC-010], [IO-007]
**Test derivation:** A ν-join over a place holding tokens of two different names;
verify only the tokens of the selected name are consumed and the others remain.

#### NU-022: Deterministic Match Selection

**Priority:** MUST
**Kind:** F

When more than one correlation name is simultaneously eligible at a matched
transition, the implementation MUST select the name with the smallest
`(oldest correlated-token timestamp, then NameId)` ordering: oldest first, ties
broken by name. The selection is a pure function of the current marking and MUST
be **identical across all conforming implementations** on names whose values hold only Basic
Multilingual Plane characters ([NU-001]): the firing tie-break
(`selectMatchName` / `select_match_name`) is byte-identical on such names, and any incremental
acceleration of it MUST return byte-identical results to the reference function.
A token a `ForwardInput` forwards on a timeout outcome keeps its original `created_at` in
every implementation ([IO-014]), so a name whose oldest correlated token was forwarded
orders the same everywhere.

A name is eligible at a matched transition when the match keys at least one input and every
correlated input holds at least one token of the name and at least the input's required count of
such tokens; a token whose key yields no name counts for no name ([NU-020]). The oldest
correlated-token timestamp of a name is the earliest `createdAt` among all tokens of the name in
the correlated inputs, whether the firing consumes them or not.

*If* some name is eligible at a matched transition, *then* the selection *shall* return a name.

*When* the selection returns a name, that name *shall* be eligible, and no eligible name *shall* precede it in the order by oldest correlated-token timestamp, then by name order.

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
**Kind:** F

Names minted in two instances never collide ([NU-010]); the transition component of a minted
name ([NU-011]) is the firing transition's post-compose name, which carries the instance prefix
unless the transition is channel-merged ([MOD-021]). The match specification of a composed join
follows the same place rewrite as its arcs ([MOD-020]), so a composed join still correlates the
renamed inputs and produces into the renamed relay targets ([NU-054]).

*When* a transition is rebuilt through a place rewrite (such as prefix renaming [MOD-010], port binding [MOD-020], place fusion [MOD-061], or the identity rewrite of action binding [CORE-042]), the set of input places of the rebuilt transition *shall* be the image under the rewrite of the set of input places of the original transition.

*When* a transition is rebuilt through a place rewrite, the set of places of the output specification of the rebuilt transition *shall* be the image under the rewrite of the set of places of the output specification of the original transition.

*When* a transition that carries a match specification is rebuilt through a place rewrite, the rebuilt transition *shall* carry a match specification whose correlated places and relay targets ([NU-054]) are the images under the same rewrite of the original ones, in the same order, each with the key projection it had.

*When* a transition that carries no match specification is rebuilt through a place rewrite, the rebuilt transition *shall* carry no match specification.

*When* a transition is rebuilt through a place rewrite, the name of the rebuilt transition *shall* be the original name with the instance prefix under prefix renaming ([MOD-010]) and the original name under every other rebuild.

**Acceptance Criteria:**
1. Two instances of a forking subnet never mint colliding names.
2. After composition, a join's match correlates the renamed (host-bound) places,
   not the author-original ones.

**Depends on:** [MOD-010], [MOD-020], [MOD-021], [MOD-061], [CORE-042], [NU-010], [NU-011], [NU-054]
**Test derivation:** Instantiate a fork+join subnet twice; verify each instance's
joins merge only their own siblings.

---

#### NU-060: Match-Arc Composition

**Priority:** SHOULD
**Kind:** F

A correlated input behaves, under channel composition ([MOD-021]), as the input
arc it layers on: its arc dedup/conflict rules are unchanged. A merge MUST NOT
silently drop a match, and no implementation fuses two matches into one: when both
merged sides carry a match, whatever places the two matches correlate, the merge
MUST be rejected with an error naming the caller-side transition.

*When* at most one side of a channel merge carries a match, the channel merge *shall* reject with the same error when the same merge of the two transitions without their matches rejects, and otherwise *shall* give the merged transition of that merge with that side's match unchanged, or with no match when neither side carries one.

*If* both sides of a channel merge carry a match, *then* the channel merge *shall* be rejected with an error that names the caller-side transition.

A correlated input is therefore merged by the canonical input-arc merge table like any
other input arc: a correlated `one()` and the other side's `one()` on the same place give
one `exactly(2)` arc that the surviving match still correlates. The other side's token on
that place is then a token of the chosen name, not the oldest token. Which error a merge reports
when it also breaks a rule of [MOD-021] is not specified.

**Acceptance Criteria:**
1. Composing a transition that carries a match with a side that carries none
   preserves the match on the flat net (it is not dropped).
2. A merge of two transitions that both carry a match is rejected with an error
   naming the caller-side transition, whatever places the two matches correlate.

**Depends on:** [MOD-021], [NU-020], [NU-054]
**Test derivation:** Channel-merge a matched transition with a passthrough side;
verify the composed transition still correlates. Channel-merge two matched transitions
whose matches key different places; verify the merge is rejected naming the caller-side
transition.

---

## Decidability — the bounded-budget ledger

#### NU-040: Bounded Budget and Decidability

**Priority:** SHOULD
**Kind:** F

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

*Where* a place is declared to the verifier as a budget place, the ν routes *shall* read every transition that has an input arc on that place as a declared mint ([NU-010]).

The ν routes *shall* read a transition named as a mint transition on the verifier (`mintTransitions` / `mint_transitions`) as a declared mint, whatever budget places are declared.

The ν routes *shall* read a transition as a declared mint only when it is named as a mint transition on the verifier or has an input arc on a place declared to the verifier as a budget place.

A read, inhibitor or reset arc on a budget place declares nothing.

**JoinedOrDeadLettered.** The property `JoinedOrDeadLettered(pending)` says that no correlation
group is left behind when the net comes to rest: no reachable quiescent marking holds a
`pending` token. A run that never comes to rest does not violate it.

Every route that decides `JoinedOrDeadLettered(pending)` *shall* count a marking as violating it when the marking is quiescent ([VER-002]) and `pending` holds a token, whether or not a declared sink place is marked.

Every route that decides `JoinedOrDeadLettered(pending)` *shall* count a marking as violating it only when the marking is quiescent and `pending` holds a token.

In that quiescence a transition with a match specification *shall* count as enabled exactly when it is enabled as [NU-020] says: on its token counts, and with a name of which every correlated input holds at least one token and at least its required count; a match that correlates no input is never enabled.

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
with the untimed encoder.

---

#### NU-050: Exact Verification of Matched Transitions

**Priority:** MAY
**Kind:** B

The untimed encoder is value-blind ([VER-004]). For ν-nets this is
relaxed under a carve-out: a matched transition's **name equality** is encoded
**exactly** rather than name-blind, so a counterexample that silently equates two
*different* names (criterion **#1** below) is ruled out. The name dimension is the
projection declared at the match ([NU-001]) — the analyzer treats it as
name-symmetric.

The exactness goal MAY be realized by either of two routes:

- **Route A — bounded name-colouring** (the budget made literal). Names are
  modeled as a finite set of `k` **colours**, where `k` is the colour-slot bound of
  [NU-053], at least the number of live names: each coloured place becomes `k`
  per-colour counts, a mint introduces a *globally fresh* colour, and a join
  consumes the **same** colour from every correlated input, so no counterexample
  equates two different names. It stays in linear arithmetic, and its `Proven` is
  sound while the declared mints and the coloured consumers keep their contracts
  ([NU-010], [NU-051]). It applies to the **mint → matched-join fragment**: coloured
  places (the matched inputs) are produced only by minting forks and consumed only by
  matched joins, each mint is declared ([NU-010]), **a colour-slot bound exists**
  ([NU-053]), and coloured places carry no inhibitor/read/reset arc. A net outside this
  fragment, including one with no colour-slot bound, falls back to the sound
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
  classes). It is sound for every executor run, and complete for the free-choice
  name semantics the graph explores ([VER-012]) whenever the symbolic graph closes
  within the class bound; an unbounded live-name pool surfaces as graph truncation,
  which never yields `Proven`. The alternative
  realization — equality over an uninterpreted **name sort** (EUF) in the CHC
  encoder — is not taken (the SMT path is untimed, and Spacer over an
  uninterpreted sort is poorly supported).

When the live correlation-name pool is **not bounded** — no budget ([NU-040]) and
no structural bound the name-partition quotient (Route B) can discover — the
verifier MUST NOT return an unsound verdict (criterion **#2** below, mirroring the
`Ignore`-mode discipline of [VER-006]); under Route B this appears as state-class-graph
truncation, and the verdict is `Unknown` unless the prefix rule below finds a violating class.

**The verdict on a built graph.** Route B reads its verdict off the classes its build stored,
in discovery order, by the prefix rule of [VER-012] AC3.

*If* the build of the Route B graph is stopped, because it runs out of total budget or is cancelled ([VER-013]), *then* Route B *shall* answer `Unknown`, whatever classes the build stored.

*If* the build is not stopped and a stored class violates a safety property, or an expanded class at which the net rests violates a quiescence property, *then* Route B *shall* answer `Violated`, also when the graph does not close.

*If* Route B answers `Violated`, *then* the class its counterexample ends at *shall* violate the property: a stored class for a safety property, an expanded class at which the net rests for a quiescence property.

*If* the build is not stopped and no class violates the property, *then* Route B *shall* answer `Proven` when the graph closes and `Unknown` when it does not.

*If* the Route B graph does not close, *then* Route B *shall not* answer `Proven`.

Under modelled injection ([VER-006]) Route B treats an environment place as an inexhaustible
input and so cannot observe its count or the names injected into it; it declines (`Unknown`)
when a verdict would depend on them ([VER-006] AC8).

On a timed net Route B gives a matched join a clock only while one name-symbol is present in
every correlated input, because the executor enables the join only then ([NU-020]). A join whose
inputs hold tokens but share no name has no clock, so its latest bound constrains no other
firing. The clock-restart rule of [TIME-012] reads the name layer too: a firing after which no
name is present in every correlated input restarts the join's clock, even when the inputs still
hold tokens, and a join whose inputs come to share a name starts a fresh clock then. This holds with
and without the latest-bound relaxation for a late executor ([TIME-013]).

*While* a transition is not enabled with an eligible name ([NU-020], [NU-022]), Route B *shall* hold no clock for it, even when its inputs hold the tokens its arcs require but no name is present in every correlated input.

*When* a transition fires and another transition `j` holds a clock and is not enabled with an eligible name ([NU-020], [NU-022]) in the intermediate marking ([TIME-012]), Route B *shall* take `j`'s clock away, even when `j`'s inputs still hold tokens, and *shall* give `j` a fresh clock if the firing leaves `j` enabled with an eligible name.

*When* a transition fires and another transition `j` holds a clock and is enabled with an eligible name ([NU-020], [NU-022]) before the firing, in the intermediate marking and after the firing, Route B *shall* keep `j`'s clock.

*When* a firing leaves a transition `j` enabled with an eligible name ([NU-020], [NU-022]) and `j` held no clock before it, Route B *shall* start `j`'s clock at that firing.

*When* a transition fires, Route B *shall* take its clock away and *shall* give it a fresh clock if the firing leaves it enabled with an eligible name ([NU-020], [NU-022]).

*While* time passes, Route B *shall* keep the marking and the start of the clock of every transition enabled with an eligible name ([NU-020], [NU-022]), and *shall* advance the clock reading by the time that passed.

Route B *shall* fire a transition only when it holds a clock that has run for at least the transition's earliest bound ([TIME-001]), and *shall* leave the clock reading unchanged at a firing.

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

**Soundness.** Both routes are sound against the untimed executor, with no environment place,
while the projections and the actions keep the contracts above.

*If* the coloured places start empty, every transition is in the fragment for its role, every key and relay projection reads the name its writer put there, and every declared mint and coloured consumer keeps its contract ([NU-010], [NU-051]), *then* Route B *shall* answer `Proven` for a safety property only if no marking the untimed executor reaches violates it.

*If* in addition every correlated input takes at least one token, *then* Route B *shall* answer `Proven` for a quiescence property only if no marking the untimed executor reaches and rests at violates it.

*If* Route A builds its plan with the colour-slot bound of [NU-053], every key and relay projection reads the name its writer put there, and every declared mint and coloured consumer keeps its contract, *then* a `Proven` of the coloured encoding of a safety property *shall* hold of every marking the untimed executor reaches.

*If* in addition no transition of the net is reapable, *then* a `Proven` of the coloured encoding of a quiescence property *shall* hold of every marking the untimed executor reaches and rests at.

**Acceptance Criteria:**
1. (**NU-050 #1**) A property whose counterexample requires two *different* names
   to be equal is not reported on the exact path, unlike the value-blind
   over-approximation.
2. (**NU-050 #2**) An unbounded-fresh-name net without a budget place never yields
   `Proven`: its Route B graph does not close, and the verdict is `Unknown` unless a stored
   class violates the property, in which case it is `Violated` by the prefix rule of
   [VER-012] AC3.
3. Two forks mint one name each into the two inputs of a join with `window(0, 5)`, and a
   watchdog marks `BAD` at `delayed(10)`. Route B reports `unreachable(BAD)` violated, on time
   and late: the join is never enabled, so its deadline does not hold back the watchdog.
4. A join at `delayed(10)` is count-enabled from 1 ms and first shares a name at 5 ms. Route B
   lets it fire at 15 ms at the earliest.

**Depends on:** [VER-004], [VER-006], [VER-012], [NU-001], [NU-010], [NU-020], [NU-040], [NU-051], [NU-053], [TIME-001], [TIME-012], [TIME-013]
**Test derivation:** Encode a join whose spurious untimed counterexample equates
two distinct correlation ids; verify the exact carve-out (Route A bounded
name-colouring) eliminates it, while a same-name join still reaches its merge.

---

#### NU-051: EXTENDED Coloured-Consumer Fragment

**Priority:** MAY
**Kind:** F

The [NU-050] Route B name-partition quotient decides the **mint → matched-join**
fragment exactly. An opt-in **EXTENDED** fragment mode widens that exact path to
two further shapes without weakening its soundness: a **coloured consumer**
(drain/relay) that removes a correlation name without a match, and **carrier
places** that thread a fork-minted name through intermediate places to a ν-join
input. The mode is a two-value knob — **BASE** (default) reproduces the shipped
mint → matched-join fragment exactly; **EXTENDED** is selected on the verifier
builder (`fragmentMode` / `fragment_mode`). Both are decided by the solver-free
Route B quotient, and by Route A where [NU-053] is offered; neither changes the canonical name-partition key
format ([VER-012]), so cross-language byte compatibility is preserved.

- **Coloured consumer (drain/relay).** Under EXTENDED, a transition with **no** match spec MAY
  consume a coloured place. The analyzer admits it only as a drain/relay role and only when it
  consumes **exactly one** coloured input at count **exactly one** ([IO-001] `One` or [IO-002]
  `Exactly(1)`). *While* the fragment mode is BASE, the fragment classifier *shall* give no role
  to a transition without a match spec that consumes a coloured place. *While* the fragment mode
  is EXTENDED, *if* a transition without a match spec consumes exactly one coloured input, at
  count one, has no reset, read or inhibitor arc on a coloured place, puts on each branch
  exactly one token, and never a drained batch, into each coloured place the branch writes, and
  on timeout writes a coloured place only by forwarding that input, *then* the fragment
  classifier *shall* give it the coloured-consumer role of that input's place, whether or not it
  is declared a mint. A coloured consumer **relays** the consumed name-symbol into each coloured
  output of the fired branch (threading the same name), or **drains** it (dead-letters the name)
  on a branch that produces no coloured output; a single `Xor` transition ([IO-012]) MAY relay
  on one branch and drain on another. *When* a coloured consumer fires on a branch with a name
  its coloured input holds, the name layer *shall* remove one token of that name from the input,
  add one token of that name to each coloured output of the branch and change no other count, so
  a branch with no coloured output drains the name. Because the consumed count is fixed at one,
  the role is identified by the input place name alone — no count, no input list. A consumer
  that consumes more than one coloured place, or consumes at any count other than one
  (`Exactly(n≥2)`, `AtLeast`, `All`), is **rejected** to the sound over-approximation: the base
  marking adds exactly one token per output place, so re-emitting a higher input cardinality
  into the name layer would over-count and could let a join fire by equating two distinct names
  (a false `Proven`). *While* the fragment mode is EXTENDED, the fragment classifier *shall*
  give a transition without a match spec that consumes a coloured place no role other than the
  coloured-consumer role of its one coloured input, and that role only when it consumes exactly
  one coloured input, at count one, and puts on each branch exactly one token, and never a
  drained batch, into each coloured place the branch writes. The fragment classifier *shall*
  give the coloured-consumer role to no other transition: to none while the fragment mode is
  BASE, to no matched transition and to no transition that consumes no coloured place.

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
  token with no name; either puts the net outside the fragment. *If* a transition without a
  match spec consumes a coloured place and its timeout writes a coloured place other than by
  forwarding that consumed input, *then* the fragment classifier *shall* give it no role.

- **Carrier places (fork-threaded co-mint).** Under EXTENDED, an author MAY declare
  intermediate **carrier** places (`carrierPlaces` / `carrier_place(s)`) that carry
  a fresh name from the minting fork ([NU-010]) onward to a ν-join input. The
  analyzer unions the declared carriers into the coloured set **before** role
  assignment, so the existing mint co-mints one fresh name into all of them.
  *While* the fragment mode is EXTENDED, the fragment classifier *shall* give roles
  against the coloured set it uses with no carrier declared, with every declared
  carrier place added and no other place. In either fragment mode, a declaration
  whose carrier places are all places of the net is accepted. A
  declared carrier name absent from the net's places MUST NOT be silently ignored,
  in either fragment mode and whatever the query:
  the implementation MUST fail loudly (reject at the builder naming the offending
  place, or surface `Unknown` with a reason naming it), because a mistyped carrier would let
  two fork branches mint independent names and produce a confident, spurious
  deadlock verdict. A refusal that does not depend on the carrier declaration, such as a
  stop before the call starts ([VER-013]), an unresolved property place ([VER-003]) or a
  declared mint that is not a transition of the net ([NU-010]), may come first, and that
  refusal is then the answer. *If* a declared carrier place is not a place of the net, *then*
  the verifier *shall* either reject the declaration, naming such a place, or answer
  `Unknown` with a reason that names at least one such place and no other place, in
  both BASE and EXTENDED and whatever the query, unless the same request with no carrier
  place declared gets the same refusal. Under BASE, the fragment classifier
  ignores declared carriers (a documented no-op); the in-flight split of [VER-004]
  reads them in both modes.
  *While* the fragment mode is BASE, the fragment classifier *shall* give roles
  against the same coloured set whatever carrier places are declared.

- **Reset/read/inhibitor-on-coloured exclusion (BOTH modes).** In **both** BASE and
  EXTENDED, the analyzer rejects a net in which **any** coloured place carries a
  reset ([CORE-034]), read ([CORE-032]), or inhibitor ([CORE-031]) arc on any
  transition. Such an arc would be misclassified `Ordinary`, letting the base step
  zero or gate the coloured place while the name layer keeps the symbol, drifting
  the name layer from the base count marking. This is a deliberate soundness
  tightening applied to BASE too (rejection just falls back to the sound
  over-approximation); it never turns a `Proven`/`Violated` into an unsound verdict. *If* a
  coloured place carries a reset, read or inhibitor arc of a transition, *then* the fragment
  classifier *shall* give that transition no role, in both BASE and EXTENDED.

- **Off-key coloured input exclusion (BOTH modes).** In **both** BASE and EXTENDED,
  the analyzer rejects a net in which a matched transition consumes a coloured place
  through an input that is **not** one of its match keys. *If* a matched transition
  consumes a coloured place through an input that is not one of its match keys, *then* the
  fragment classifier *shall* give it no role, in both BASE and EXTENDED. Such an input consumes
  FIFO ([NU-020]), whatever the token's name, so the name layer cannot know which
  name leaves the place: Route B would keep the symbol and Route A would force the
  join's shared colour on it. A non-coloured non-key input (a budget or permit) is
  unaffected. Rejection just falls back to the sound over-approximation.

- **Diagnosability.** When EXTENDED is requested but the net falls outside this
  fragment, the verifier MUST surface a short note (the "EXTENDED declined" note: a
  report line saying that the exact ν path was not taken and why, in words the
  implementation chooses) rather than silently falling back, so an author can tell the exact path was not
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
4. (MUST) In both BASE and EXTENDED and whatever the query, a declared carrier place
   not present in the net fails loudly (builder rejection naming the place, or `Unknown`
   with a reason naming the place), unless a refusal that does not depend on the declaration
   is the answer; it is never silently ignored.
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
carrier name fails loudly in both modes; a join consuming another join's key off-key is rejected in
both modes and its reachable stranding is not proven; an end-to-end `deadlockFree` / `JoinedOrDeadLettered`
query on a fork-threaded co-mint plus drain fixture PROVES via Route B and turns
VIOLATED when the drain is removed.

---

#### NU-052: Conflict-Only Priority for the Route B Name-SCG

**Priority:** MAY
**Kind:** F

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
  demand is the sum of the required counts ([IO-007]) of that transition's input arcs
  on `p`: 1 for `One` and `All`, `n` for `Exactly(n)` and `AtLeast(n)`). Read and
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

*While* the mode is `CONFLICT`, the Route B graph *shall* leave a base-enabled transition `L`
unexpanded from a class exactly when another transition `H` of the net pre-empts `L` in that
class, and *shall* expand every other base-enabled transition of the class as under `NONE`, in
the same order.

*While* the mode is `CONFLICT`, the Route B graph *shall* take two transitions `H` and `L` to
compete in a class exactly when some place is a consumed input of both and its token count in
the class marking is less than the sum of their demands on it, where a transition's demand on a
place is the sum of the required counts ([IO-007]) of its input arcs on that place.

*While* the mode is `CONFLICT`, the Route B graph *shall* take `H` to be ready no later than `L`
in a class exactly when `readyEarliest[H] <= readyEarliest[L]` within a float epsilon, where
`readyEarliest` is the DBM lower bound of each enabled clock before time is let to pass.

The default mode, `NONE`, MUST reproduce the prior Route B behaviour byte-for-byte.

*While* the mode is `NONE`, the Route B graph *shall* expand each base-enabled transition of a
class, in the class's clock order (the code-point order of the transitions' names, [VER-010]
AC1), with the successors the transition has when it is expanded alone from the same class and
the same base layer, *shall* expand no other transition, and *shall not* read the readiness,
in-flight state or competition of any transition.

*While* the mode is `NONE`, the Route B graph *shall* give a base-enabled transition at least one
successor labelled with its name when the base layer can fire one of its branches in the class
and the transition will fire on the name layer (always for an ordinary or minting transition,
with an enabling name for a join, with a resident name for a consumer).

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
verifier MUST, whenever conflict priority applies to a call (below), split every pruner
`H` (a transition with strictly higher priority than another it shares a consumed input
with) and every transition that deposits into an input or read place of a pruner, except a
transition that models an environment or is a completion step ([VER-004]), and MUST NOT
let `H` pre-empt anything while `inflight:<H>` is marked. When one of those transitions
cannot be split (a ν-join, or a writer into a coloured place, [VER-004]), the pruning is
off for that call: the verdict is the `NONE` verdict and the report names the transition,
unless the split without the pruning is refused as well, when the call answers `Unknown`
with that refusal. The idiom above is such a case, because the join is a pruner and cannot be
split. Under `assumeAtomicFiring` nothing is split and the pruning stays on, and the report
states the atomic assumption. A direct call to Route B (Rust `verify_via_name_scg`,
TypeScript `verifyViaNameScg`) applies no split and prunes as before; the in-flight guard
has no effect on a net without in-flight places.

Conflict priority does not apply to a call on a net with a transition read as reapable
([VER-002]); under `assumeNoReaping` none is. A late executor reaps a reapable pruner and then
fires the transition it would have pre-empted, so no firing can be pruned for it.

*While* the mode is `NONE`, conflict priority *shall not* apply to any call, and the verifier
*shall* hand the in-flight split ([VER-004]) the `QuiescentCount` demand alone.

*While* the mode is `CONFLICT`, conflict priority *shall* apply to a call exactly when no
transition of the net is read as reapable ([VER-002]) and either the property is a
name-alignment one ([NU-055]) or the net has a ν-join and the property is not a
reachability-safety one with a declared budget place ([NU-050]), and the verifier *shall*
verify every other call as under `NONE`.

*While* conflict priority applies to a call and `assumeAtomicFiring` is set, the verifier
*shall* keep conflict priority on.

*While* conflict priority applies to a call and `assumeAtomicFiring` is not set, *if* the net
has no pruner or every transition the verifier would split under conflict priority can be
split, *then* the verifier *shall* split every pruner and every transition that deposits into
an input or read place of a pruner, except a transition that models an environment or is a
completion step ([VER-004]), and *shall* keep conflict priority on.

*While* conflict priority applies to a call and `assumeAtomicFiring` is not set, *if* the net
has a pruner and a transition the verifier would split under conflict priority cannot be split,
*then* the verifier *shall* hand the in-flight split and Route B what it hands them under
`NONE`, so the verdict is the `NONE` verdict, and *shall* name the first such transition, in the
transition order, in the report, unless the split under `NONE` is refused too, when the call
answers `Unknown` with that refusal ([VER-004]).

*While* the mode is `CONFLICT`, the Route B graph *shall* take a transition `H` to have a firing
in flight in a class exactly when the class marking holds a token on the place `inflight:<H>`.

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

**Depends on:** [VER-012], [NU-050], [NU-020], [VER-004], [VER-002], [VER-010], [IO-007],
[NU-055], [CONC-002], [EXEC-002], [EXEC-003]
**Test derivation:** the minimal ν-join vs. timed dead-letter-drain fixture is
`Violated` under `NONE` and `Proven` under `CONFLICT`; a genuine orphan is `Violated`
under `CONFLICT` without a drain and `Proven` with one; every verdict is attributed
to Route B.

---

#### NU-053: EXTENDED-Coloured Quiescence in the Route A SMT Encoder

**Priority:** MAY
**Kind:** F

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
- encodes the **quiescence** of [VER-002] colour-aware, for each quiescence property
  (`DeadlockFree`, `TerminatesAtSink`, `JoinedOrDeadLettered`, `QuiescentCount`): every
  transition that is not reapable is disabled for an uncoloured reason (an uncoloured input
  below its demand, a marked inhibitor or an empty read place) or for every colour (a mint
  has no globally-fresh colour, a join no shared colour, a consumer no resident colour), and
  the property conjoins its own clause over the all-colour token counts, so
  `JoinedOrDeadLettered` carries no sink clause ([NU-040] AC4). The encoding has no
  environment-injection rule, so it does not answer when injection is modelled ([VER-006]
  AC7);
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
  every flat transition, `k = ⌊y·M0⌋`, `k ≤ 2^31 − 1`). A weighting that fails the re-check is discarded and
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

*When* the coloured encoding decides a quiescence property, it *shall* treat an encoding state as violating exactly when every flat row (each XOR branch is its own row) whose transition is not reapable ([VER-002]) is disabled in the state for an uncoloured reason or, when the row touches a coloured place, for every colour below `k`, and the property's own clause holds of the state's all-colour token counts.

*If* the verifier sets the colour-slot bound to `k`, *then* some covering weighting `y` *shall* have `⌊y·M0⌋ = k`, and no covering weighting *shall* have `⌊y·M0⌋ < k`, a covering weighting being one with `y ≥ 0`, `y_p ≥ 1` on every coloured place and `y·C_t ≤ 0` on every flat transition.

*If* the verifier sets the colour-slot bound to `k`, *then* the exact re-check *shall* have accepted a weighting and given it the bound `k`.

The exact re-check *shall* accept a weighting `y` exactly when `y ≥ 0`, `y_p ≥ 1` on every coloured place, `y·C_t ≤ 0` on every flat transition and `⌊y·M0⌋ ≤ 2^31 − 1`, and *shall* give an accepted weighting the bound `⌊y·M0⌋`.

The update of a coloured consumer, per colour `c`, emits `(- x 1)` for its input column
and `(+ x 1)` for each coloured output column. A consumer that relays into its own
input (a self-loop, `spin: a, tick → a, tock` with `a` coloured) gets **no** update term
for that column: it keeps its `>= 1` guard and is carried over unchanged, as a join's
key that is also a relay target is ([NU-054]). A rule updates each column once, so
emitting both terms would keep only the `(+ x 1)` and leave the consumer unable to fire
under any law that weights `a`.

*When* the coloured encoding emits the rule of a coloured consumer for a colour `c` below `k`, the rule *shall* be enabled only when colour `c` of the input holds a token, and *shall* subtract one from colour `c` of the input, add one to colour `c` of each coloured output, and leave unchanged colour `c` of a place that is both the input and an output and every other colour column.

The verifier routes a bounded quiescence query to Route B first; when Route B
truncates (`Unknown`), it **defers** to this scalable Route A encoding rather
than returning `Unknown`. A verdict from the coloured plan is not downgraded as a
name-blind verdict would be (the colour-aware deadlock does not over-fire joins); only the
`Ignore` downgrade of [VER-006] applies to it. Its `Proven` is sound while the
declared mints and the coloured consumers keep their contracts ([NU-010], [NU-051]);
the report prints the colour-slot bound as `colour-slot bound k=<k>`, after the
`Colour-slot bound:` line below, and names the transitions whose contracts it assumes.

The verifier *shall not* run Route B ([VER-012]) after the colour-slot bound in one verification call.

*When* the verifier runs the colour-slot bound for a `DeadlockFree`, `TerminatesAtSink`, `JoinedOrDeadLettered` or `QuiescentCount` property, it *shall* have run Route B ([VER-012]) in the same verification call.

The verifier *shall not* run the colour-slot bound on a net without a ν-join or without a declared budget place, or when environment injection is modelled or an arrival feeds a coloured place ([VER-006]).

*When* Route B builds its name-partition graph for a `DeadlockFree`, `TerminatesAtSink`, `JoinedOrDeadLettered` or `QuiescentCount` property of a ν-net with a declared budget place and the graph returns `Unknown`, the verifier *shall not* return that `Unknown` from Route B and *shall* hand the query over to the next phase of the dispatch.

*When* the verifier has built the coloured plan and the call is not under `Ignore` with environment places registered, the fixpoint query *shall* decide with the verdict of the coloured query and *shall not* downgrade it.

*When* the verifier has not built the coloured plan for a `DeadlockFree`, `TerminatesAtSink`, `JoinedOrDeadLettered` or `QuiescentCount` property of a ν-net with a ν-join, the fixpoint query *shall not* return `Proven`.

**The solve is normative**, so every implementation performs the same pivots, returns the
same weighting and refuses the same nets:

1. *Presolve.* `U` is the least set of places containing the coloured ones such that a flat
   transition producing into `U` has every place it consumes from in `U`. The kept rows are
   the transitions producing into `U`, in flat order, restricted to `U`; a kept row equal to an
   earlier one after the restriction is dropped. `<n>` and `<m>` in the report lines are the
   presolved sizes: `|U|` and the number of kept rows.
2. *Tableau.* The dual in standard form, maximise `c·σ` subject to `A·σ + s = b`,
   `σ, s ≥ 0`: one constraint row per place `U[i]`, ascending (`A[i][j]` is `pre − post` of kept
   row `j` at `U[i]`, `b_i = M0[U[i]]`), and `c_j` the net production of kept row `j` into the
   coloured places. Columns are the kept rows, then the slacks in the order of `U`; the slacks
   are the initial basis.
3. *Bland's rule.* Entering: the smallest column with a negative objective-row entry; none
   means optimal. Leaving: the least ratio `rhs_i / a_ie` over rows with `a_ie > 0`, ties to the
   row whose basic column is smallest; none means the program is infeasible. The weighting is
   `y_p = π_i + [p coloured]` for `p = U[i]`, `π_i` the objective-row entry of slack `i`, and
   `y_p = 0` off `U`.
4. *Limits.* A program over more than 4096 places or 16384 rows after the presolve is refused
   before any pivot. The **work** of a pivot on row `r` and column `e` is the number of non-zero
   entries of row `r`, plus, for every other constraint row with a non-zero entry in column `e`
   and for the objective row when it has one, that row's non-zero count plus row `r`'s, all
   counted before the pivot and slack entries included; the work of a solve is the sum over its
   pivots, and it MUST NOT exceed 4000000. Every tableau entry (constraint rows, right-hand
   sides, objective row and value) MUST have numerator and denominator in lowest terms at most
   `2^63 − 1` in absolute value: the initial tableau is checked before any pivot, and every
   entry a pivot writes is checked after it, that pivot counted. Each round decides in this
   order: no entering column, optimal; no leaving row, infeasible; the next pivot's work past
   the limit, refused; a stop ([VER-013]), stopped; otherwise pivot, then the coefficient check.

The limits bound the time of the solve whether or not a total budget is set.

*When* the verifier solves the colour-slot program of a flat net with `n` places and `m` transitions that has a covering weighting `y` with `⌊y·M0⌋ ≤ 2^31 − 1`, and `n ≤ 4096`, `m ≤ 16384`, `C(n+m, n)·(2n+1)·(n+m+1) ≤ 4000000` and `(n+1)!·E^(n+1) ≤ 2^63 − 1`, where `E` is the largest of 1, every initial count and `n` times every `pre + post` of a flat transition at a place, it *shall* set a colour-slot bound unless the solve is stopped ([VER-013]).

On such a net the solve reaches no limit. Bland's rule never returns to a basis, so the solve makes
fewer than `C(n+m, n)` pivots, and a pivot's work is at most `(2n+1)·(n+m+1)`. Every tableau entry
in lowest terms is a ratio of two minors of the initial tableau, and each minor is at most
`(n+1)!·E^(n+1)` in absolute value. The optimal weighting the solve reads off is an exact
optimum, so it passes the re-check, and by the sentences above the bound is `⌊opt⌋`.

The report line is one of:

```
  Colour-slot bound: LP optimum <opt> over <n> places and <m> transitions, so k=<k> (re-checked in exact arithmetic)
  Colour-slot bound: none (LP infeasible over <n> places and <m> transitions: no weighting bounds the coloured tokens)
  Colour-slot bound: none (LP over <n> places and <m> transitions exceeds the limit of 4096 places and 16384 transitions)
  Colour-slot bound: none (no LP optimum within the work limit of 4000000 entry updates, after <pivots> pivots)
  Colour-slot bound: none (an LP coefficient outgrew 63 bits after <pivots> pivots)
  Colour-slot bound: none (LP weighting failed the exact re-check: <reason>)
```

On every line but the first no plan is built and the query falls back as for an infeasible
program; a stopped solve prints no line and reports the stop instead. The shared fixture
`spec/verification-fixtures/slot-bound-lp.json` pins each case's status, pivots and work, and
for a solved case its presolved sizes, optimum, `k` and weighting, for every implementation.

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
   infeasible), an unbounded colour leak such as an over-refund that inflates the *minting*
   budget or a relay that refunds and frees a token for a `(k+1)`-th colour, falls back to the
   sound over-approximation rather than a false `Proven`. (A refund to a *non-minting*
   place keeps the minting budget a covering weighting, so it stays bounded and is
   admitted: the structural bound is more precise than the old budget-conservation
   heuristic.)
5. A leaky co-mint fan-out — a fork co-minting one colour into a place the refunding
   join never re-collects (e.g. an un-drained carrier) — falls back rather than a
   false `Proven`: the colour would otherwise outlive its budget and the k-colour
   encoding would under-approximate.
6. A slot-bound optimum below one (a mid-phase marking with no budget token, or an
   `exactly(3)` fork from one budget token, optimum `2/3`) yields the exact plan with
   `k = 0`: quiescence is decided, never downgraded to `Unknown` as a name-blind verdict would
   be, and the emitted encoding is
   well-formed with zero colour slots. The program is a relaxation over the reals, so a mint
   that can never fire does not always give `k = 0` (an `exactly(2)` fork from one budget
   token that a join refunds has optimum 1). The plan is still refused when the program is
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
   one on a coloured place or increasing along a flat transition, or one whose bound
   `⌊y·M0⌋` exceeds `2^31 − 1`, refuses the plan with the
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
**Kind:** F

A matched join ([NU-020]) consumes a name and, in the analysed fragment, may not write a name
onto a coloured place: the analyzers read any coloured output of a join as a re-mint and reject the
net to the over-approximation. That blocks two shapes that are routine in object-centric models: a
**join chain**, whose join hands the matched name on to a later join (`e: C1, D1 → P5` followed by
`f: P5, OR → R`), and a **correlated self-loop**, whose join writes the matched name back onto one
of its own keys (`B: p, Y1 → Y1, w, q`). Five of the eleven ν transcriptions of the PNID figures
in `research/net-metrics/validation/pnid/` fall back for this reason alone, and every quiescence
property on them comes back `Unknown`.

**Declaration.** A match specification MAY declare **relay targets**: output places onto which the
join writes the name it matched, each with a key projection like a match key's, from a token's
value to a `NameId` or to no name ([NU-020]).
Every relay target MUST appear in the transition's output spec (in at least one branch), and a
place MUST NOT be declared twice; either violation is rejected when the transition is built, naming
the transition and the place. A relay target MAY also be one of the join's own match keys (the
self-loop). Under composition the relay targets are remapped by the same place rewrite as the keys
([NU-030], [NU-060]). A rewrite that maps two relay targets of one join onto one place (fusion or
port binding) produces a relay target declared twice and is rejected at rebuild with the same
error, as the other collisions of [MOD-020] are.

*If* the match specification of a transition declares one place as a relay target twice, *then* building the transition *shall* fail.

*If* the match specification of a transition declares as a relay target a place that its output spec does not name, *then* building the transition *shall* fail.

*When* the match specification of a transition declares one of its own match keys as a relay target and the transition passes every other build-time check, building the transition *shall* succeed.

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

*While* output validation is on, *when* a transition with a match specification fires, no token the firing deposits into one of its relay targets *shall* have a name other than the chosen name under that relay target's key projection, whichever output branch or timeout outcome deposited it.

*While* output validation is on, *when* a transition with a match specification fires, every token the firing deposits into one of its relay targets *shall* have a name under that relay target's key projection, whichever output branch or timeout outcome deposited it.

*While* output validation is on, *if* the output the action of a transition with a match specification returns, or the timeout outcome of its firing, puts into one of the transition's relay targets a token that has no name, or a name other than the chosen name, under that relay target's key projection, *then* the executor *shall* fail the firing with a TransitionFailed event ([EVT-008]) and *shall* deposit none of the tokens of that output or outcome.

*When* the executor fails a firing of a transition with a match specification, it *shall not* deposit any token of the firing's output or timeout outcome, *shall not* restore the tokens the firing consumed, and *shall not* withdraw a batch the action flushed before the firing failed ([IO-015]), whether the executor has already deposited that batch or still holds it queued ([EXEC-021], [CONC-003]).

*While* output validation is on, *if* a batch that the action of a transition with a match specification publishes before it completes ([IO-015]) puts into one of the transition's relay targets a token that has no name, or a name other than the chosen name, under that relay target's key projection, *then* the executor *shall not* deposit that batch, *shall* fail the firing, and *shall* deposit neither the output the action returns nor the timeout outcome of the firing.

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
the colour-slot bound is unchanged in kind: the relay targets are coloured places, so the colour-slot
program of [NU-053] weights them at least one like any coloured place, and a net whose program is
infeasible falls back as it does today.

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
meaning plain. A verifier that meets a relay declaration under BASE MUST say in its report that
the declaration was ignored and name EXTENDED. The runtime check is independent of the mode.

*While* the fragment mode is BASE, the fragment classifier *shall* give no role to a matched transition that writes a coloured place in any of its outcomes, whatever relay targets it declares.

*While* the fragment mode is EXTENDED, the fragment classifier *shall* give no role to a matched transition that writes, in any of its outcomes, a coloured place it does not declare as a relay target.

*If* the timeout outcome of a matched transition writes a coloured place by anything other than a forward of one of its match keys, *then* the fragment classifier *shall* give it no role, in both BASE and EXTENDED.

*While* the fragment mode is EXTENDED, *if* a matched transition has no reset, read or inhibitor arc on a coloured place, puts on each branch exactly one token, and never a drained batch, into each coloured place the branch writes, writes coloured places only among its relay targets, consumes coloured places only through its match keys, consumes each match key at a fixed count (`One` or `Exactly`), and on timeout writes a coloured place only by forwarding one of its match keys, *then* the fragment classifier *shall* give it the join role with the relay targets it declares.

*While* the fragment mode is EXTENDED, *when* the fragment classifier gives a matched transition the join role, the role *shall* carry as relay targets exactly the relay targets the transition declares.

*While* the fragment mode is BASE, *when* the fragment classifier gives a matched transition the join role, the role *shall* carry no relay targets.

*While* the fragment mode is BASE, the fragment classifier *shall* give a matched transition the role it gives the same transition without relay targets.

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
   `xor(and(C, E), timeout(C))`, where `E` is a sink, `deadlockFree` is not `Proven`, and neither
   Route B nor Route A decides it. The same chain with `timeout(forwardInput(A, C))` as the second
   alternative is still `Proven` through Route B. (The action alternative writes `E` so that the
   two alternatives claim different sets ([IO-012]).)
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
- Export draws the output edge to a relay target as a plain output edge; only the input edges of match keys are decorated ([EXP-018]).

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

#### NU-055: Name Alignment

**Priority:** MAY
**Kind:** F

The ν properties of [NU-040] and [VER-002] count tokens. Some contracts are about which name the
tokens carry. A search box that shows the results of the latest query should hold one name in the
place that records the query and in the place that shows its results; a stale reply that lands
after the user has typed again breaks that while every count stays in range. An implementation MAY
offer two properties that read the name layer of Route B ([NU-050], [VER-012]):

- **NameAligned(S)**, for a non-empty list `S` of places: in every reachable marking, the places of
  `S` together hold at most one distinct name. For places `p` and `q` of `S`, the same place
  included, and the name-symbols `s` and `t`: `s` resident in `p` and `t` resident in `q` imply
  `s = t`. An empty place imposes nothing, but a place holding two names violates it whatever the
  others hold, so the singleton `NameAligned(p)` says that `p` never holds two names.
- **QuiescentNameAligned(S)**: the same predicate, read only in the reachable quiescent markings.
  Quiescence is the reap-aware quiescence of [VER-002]: on the graph, an expanded class every
  firing out of which is of a reapable transition. Like `JoinedOrDeadLettered` ([NU-040]) it
  carries no sink clause: declared sink places ([VER-002], [VER-014]) do not weaken it.

*Where* name alignment is offered, `NameAligned(S)` for a non-empty `S` *shall* hold on a class of the graph exactly when, for places `p` and `q` of `S`, the same place included, every name-symbol resident in `p` equals every name-symbol resident in `q`.

`NameAligned` is a reachability-safety property and `QuiescentNameAligned` a quiescence property,
for every rule of [VER-012] that distinguishes the two (the early stop of AC5, the prefix rule of
AC3). The predicate compares names only for equality, so it is invariant under any permutation of
the name-symbols. It is therefore a function of the canonical key of a class ([VER-012] AC2), and
deciding it on the name-permutation quotient decides it on the graph.

*When* the graph closes, Route B *shall* answer `Proven` for `NameAligned(S)` exactly when every class of the graph is name-aligned on `S`, and for `QuiescentNameAligned(S)` exactly when every class of the graph at which the net rests is.

`S` keeps the order the caller gives. Its places compare by name, and a place listed twice counts
once, at its first occurrence, so `NameAligned(box, list, box)` is `NameAligned(box, list)`. An
empty `S` MUST be rejected where it is constructed, as the language reports a caller's error,
rather than yield a verdict. The order of `S` changes no verdict; it fixes the description and
which place a reason names.

**Coloured places only.** Every place of `S` MUST be a coloured place of the fragment Route B
classified for the call: match keys ([NU-020]), declared carriers ([NU-051]) and relay targets
([NU-054]). An uncoloured place carries no name in the name layer, so the predicate on it holds
vacuously and a `Proven` would say nothing about the net. A place that is uncoloured, or absent from
the net (the net does not declare it and the initial marking does not mark it), MUST fail loudly: the
verdict is `Unknown`, never `Proven`, and where no earlier refusal of the refusal order below applies,
its reason names a place of `S`: the first absent place of `S`, otherwise the first uncoloured one.
A place that a mint or a coloured consumer writes is coloured only when it is one of these, which is
why the worked example declares `inflightA`, `inflightB` and `list` as carriers. The coloured set is
the one the classifier computes for the call (Rust `coloured_order`, the `co` of the Lean
theorems), not a set the caller names.

The name a carrier or relay target holds is the name the analysis threads into it. No projection
reads a carrier, so that this name is the name the token's value is about rests on the documented,
unchecked contract of the coloured consumers that write it ([NU-051]): a `fetchA` whose action
answered a different query than the name it relays would still prove aligned. The property is
exactly as faithful to what a token carries as those contracts are.

The coloured places MUST start empty (the `hempty` premise of the Lean theorems). A call whose
initial marking holds a token in a coloured place (a restored marking, [CORE-073], [NU-011]) is
`Unknown`, and where no earlier refusal of the refusal order below applies, its reason names the
place, the first in code-point order of place names when several are marked; since nothing else
decides the property, there is no fallback.

**EXTENDED.** Under **BASE** the coloured set is the match keys alone ([NU-051], [NU-054]), so a
property place that is a carrier or a relay target is uncoloured there. Such a call is refused at
step 2 or at step 6 of the refusal order below unless an earlier step refuses it, and the reason of
either step MUST name EXTENDED. A net outside the EXTENDED fragment gets the "EXTENDED declined" note of [NU-051] and the
verdict `Unknown`. For a name-alignment property the note MUST NOT say that the property was
verified by another route; it says the verdict is `Unknown`.

**Route B only.** Route A ([NU-050], [NU-053]), the name-blind SMT pipeline ([VER-001]), the linear
bound ([VER-015]), the state-equation and firing-bound phases ([VER-018], [VER-019]), the bounded
witness phase ([VER-025]), the bounded enumeration ([VER-017]) and the structural checks ([VER-020]) do not see names. None of them decides a
name-alignment property: called directly, each returns no verdict, or `Unknown` with a reason
saying that it is decided only by the name-partition graph, and the dispatcher MUST NOT defer a
Route B `Unknown` to any of them (no [NU-053] fallback). The script encoders (`encodeScripts`,
`encode_scripts`, `encode_smt_scripts`) return no script for these properties.

A name-alignment query goes to Route B whatever the shape of the net: it needs no matched
transition, only a coloured fragment. For every other property the classifier returns no fragment
for a net without a matched transition and the dispatcher sends such a net to the flat phases; an
implementation MUST lift both gates for the name-alignment properties, and only for them. The
dispatcher sends a name-alignment property to Route B before its other routing tests: a declared
budget place, which keeps a reachability-safety property on Route A ([NU-050]), does not apply.

**Modelled injection.** Under `AlwaysAvailable` or `Bounded(k)` ([VER-006]) the decline rule of
[NU-050] and [VER-006] AC8 applies to both properties. In addition, under these modes
`QuiescentNameAligned` with a registered environment place that the net declares is `Unknown`, and
where no earlier refusal of the refusal order below applies, nor an earlier rule of its step 5, the
reason names the first such place in code-point order and points to `Arrivals` ([VER-006]); the
vacuity reading of [VER-006] AC6 does not apply to it. Route B keeps
an environment place inexhaustible and never consumes it. A net that reads input from one (say, a
keystroke stream into `first` and `retire`) therefore has no resting class in the graph, and the
vacuity reading would turn any graph of it that closes into `Proven`, even on a misaligned net,
while the executor rests misaligned between keystrokes. On the worked example the graph does not
close at all (each keystroke mints a name that can wait in `inflightB`), so the verdict would be a
truncation `Unknown`; the rule makes the reason name the environment place instead. Under `Arrivals` the
net has no environment places left ([VER-006]); the decline of [VER-006] AC10 for an arrival into
a coloured place still applies.

**Refusal order.** A call can meet several of these refusals at once. Its verdict is `Unknown` with
the reason of the first that applies, in this order, so every implementation names the same place:

1. The refusals that precede every route for every property, in this order: a call cancelled or
   out of total budget before it starts ([VER-013]); a place of `S` that the net does not declare
   and the initial marking does not mark ([VER-003] AC5), naming the first such place of `S`; a
   `Bounded(k)` environment outside its premises ([VER-006] AC3); the in-flight refusal of
   [VER-004].
2. The net is outside the fragment of the mode even when every transition counts as a mint: the
   fragment decline of the mode, under EXTENDED the note of **EXTENDED** above, under BASE a decline
   that names EXTENDED.
3. Under `Arrivals(k)` or `Arrivals(min, max)`, an arrival into a coloured place ([VER-006] AC10),
   naming the first such place in the order the environment places were registered.
4. The net is outside the fragment only because a transition writes a coloured place without
   consuming one and is not a declared mint: the decline names those transitions in declaration
   order ([NU-010]).
5. Under `AlwaysAvailable` or `Bounded(k)`, an environment place Route B cannot model ([VER-006]
   AC8). The rules run in this order, each over the environment places the net declares in
   code-point order of names: one that is coloured; one that an inhibitor arc tests (naming the
   first such transition in code-point order); where conflict priority is in effect ([NU-052]), one
   that two or more transitions consume; then, for `QuiescentNameAligned`, the first of them (**Modelled
   injection** above), and for `NameAligned`, the first that is in `S`.
6. The first place of `S`, in the order of `S`, that is not coloured. Under BASE the reason also
   names EXTENDED.
7. A coloured place the initial marking marks: the first in code-point order of place names.

Steps 3 and 5 apply whether or not the coloured places start empty. A declared mint or carrier that is not in the net is the caller's
error and is reported as [NU-010] and [NU-051] say, outside this order. The `Ignore` downgrade of a
`Proven` ([VER-006]) and a truncation `Unknown` are not refusals: they follow a graph that was
built.

*If* a name-alignment call meets a refusal of step 1 of the refusal order, *then* the verifier *shall* answer `Unknown` with the reason of the first refusal of step 1 that applies, in the order step 1 lists them, naming for an absent place the first place of `S` that the net does not declare and the initial marking does not mark.

*If* no refusal of step 1 applies and the net is outside the fragment of the mode even when every transition counts as a mint, *then* the verifier *shall* answer `Unknown` with the fragment decline of the mode, whose reason names EXTENDED under BASE.

*If* no refusal of steps 1 and 2 applies and, under `Arrivals(k)` or `Arrivals(min, max)`, an arrival feeds a coloured place, *then* the verifier *shall* answer `Unknown` naming the first such place in the order the environment places were registered.

*If* no refusal of steps 1 to 3 applies and transitions write a coloured place without consuming one and are not declared mints, *then* the verifier *shall* answer `Unknown` naming those transitions in declaration order.

*If* no refusal of steps 1 to 4 applies and, under `AlwaysAvailable` or `Bounded(k)`, a rule of step 5 applies, *then* the verifier *shall* answer `Unknown` naming the first environment place, in code-point order, that the first applicable rule finds, and for an inhibitor arc also the first transition in code-point order that tests it.

*If* no refusal of steps 1 to 5 applies and a place of `S` is not coloured, *then* the verifier *shall* answer `Unknown` naming the first such place in the order of `S`, and under BASE the reason *shall* also name EXTENDED.

*If* no refusal of steps 1 to 6 applies and the initial marking marks a coloured place, *then* the verifier *shall* answer `Unknown` naming the first marked coloured place in code-point order of place names.

*If* no step of the refusal order applies, *then* the verifier *shall not* refuse the call with a refusal of that order: unless the call is the caller's error of a declared mint or carrier that is not in the net, or a later poll sees a stop ([VER-013]), Route B builds the graph, and the verdict is the one it reads off that graph.

**Truncation.** A graph that does not close within the class bound never yields `Proven` (Lean
`Decide.truncated_never_proven`). The prefix rule of [VER-012] AC3 applies: a `NameAligned`
violated by a stored class, or a `QuiescentNameAligned` violated by an expanded class at which the
net rests (every firing out of it is of a reapable transition; with nothing reapable, an expanded
class with no successor, Lean `Decide.quiescentAt`), is `Violated` with the shortest witness in
the explored graph and a report line naming the truncation; otherwise the verdict is `Unknown`.

*If* the graph does not close, because the build reaches the class bound, runs out of total budget or is cancelled ([VER-013]), *then* Route B *shall not* answer `Proven` for either property.

*If* the graph does not close and the prefix rule finds no violation, *then* Route B *shall* answer `Unknown`.

**Violated.** A counterexample is reported as every Route B counterexample is ([VER-003],
[VER-012]): the shortest path in the name-partition graph from the initial class to a violating
class, attributed to Route B, with `counterexampleConfirmed` absent (the trace is a path of the
graph, not of the flat abstract semantics) and `counterexampleTiming` set by [VER-003]. The graph
expands every base-enabled firing and lets a coloured consumer take any resident name, where the
executor takes the oldest token ([EXEC-010]); a run of the net follows the trace when the executor's
order meets the graph's choice.

*If* Route B answers `Violated` for either property, *then* the class its counterexample ends at *shall* violate the property.

**Soundness.** Lean `Novel/RouteB/Aligned.lean` (`routeB_untimed_nameAligned_sound`,
`routeB_untimed_quiescentNameAligned_sound`) proves: for the **untimed, environment-free executor
with atomic firings**, a `Proven` of either property holds in every marking that executor reaches
(for the quiescent form, every marking at which it rests): the tokens in the places of `S` all
carry the same name. The premises are:

- the coloured places start empty;
- the mints and coloured consumers keep their contracts ([NU-010], [NU-051], [NU-054]);
- the projection contract of [NU-050]: every match-key and relay projection reads one name per
  token, the name its writer gave it, agreeing across keys and relays and never returning no name
  (Lean `Exec.ProjCoherent`, built into the model, checked by no implementation);
- every firing writes one token to each output place its branch names ([IO-016] AC4). A mint or
  relay that writes two tokens carrying different names into `box` is exactly the kind of firing
  that would falsify a `Proven` alignment;
- every place of `S` coloured, which the refusal above enforces;
- the conditions the classifier establishes (`InFragment`), unguarded inputs, and, for the
  quiescent form, join keys that consume at least one token (`PosKeys`).

*If* the premises above hold, *then* Route B *shall* answer `Proven` for `NameAligned(S)` only if the tokens in the places of `S` all carry the same name in every marking the untimed, environment-free executor with atomic firings reaches.

*If* the premises above hold, *then* Route B *shall* answer `Proven` for `QuiescentNameAligned(S)` only if the tokens in the places of `S` all carry the same name in every marking that the untimed, environment-free executor with atomic firings reaches and rests at, resting being read with the reapable set of the call ([VER-002]).

The proof reads the predicate on the executor's name view (`alignedAll_view_iff`) and shows that an
uncoloured place of `S` adds nothing to it (`alignedAll_uncoloured`), which is why that case is not
allowed to prove. Order and repeats in `S` do not change it (`alignedAll_congr_mem`).
Conflict-only priority ([NU-052]) applies as it does to every Route B property.

The proof does not cover what the shipped Route B computes on every net. Route B builds the timed
name × time graph (with the latest bounds dropped as [VER-002] requires), and its agreement with a
timed executor is not proved (gap R6 of `Novel/RouteB/Sound.lean`). This includes the all-immediate
worked example below. The Lean model also has no in-flight state. Informally, and not proved: the
predicate stays true when tokens are removed, and on a net without inhibitor, reset or drain arcs
a marking with actions in flight holds a subset of the tokens of a marking that an atomic run of
the graph's semantics reaches, where a coloured consumer may take any resident name. A FIFO atomic
run does not always reach one: on the buggy variant below, with `fetchA` and `fetchB` both in
flight, `staged` can hold the second name while `listEmpty` is still marked. So the in-flight
markings are covered by the graph for `NameAligned`, not by the atomic executor.

**Worked example (search as you type).** Uncoloured places `typed` (2 tokens, two keystrokes),
`idle` (1), `armedA`, `armedB`, `clr`, `ready`, `listEmpty` (1), `slot` (1); coloured places `box`,
`inflightA`, `inflightB`, `reply`, `staged`, `list`, all empty at the start. Under EXTENDED, with
`sendA` and `sendB` declared mints and `inflightA`, `inflightB`, `list` declared carriers:

| Transition | Firing | Role |
|---|---|---|
| `first` | `idle, typed → armedA` | ordinary |
| `retire` | `box(n), typed → armedB` | coloured consumer, drain |
| `sendA` | `armedA → box(n'), inflightA(n')` | declared mint (first query) |
| `sendB` | `armedB → box(n'), inflightB(n')` | declared mint (follow-up query) |
| `fetchA` | `inflightA(n) → reply(n)` | coloured consumer, relay (the action calls the API) |
| `fetchB` | `inflightB(n) → reply(n)` | coloured consumer, relay (the action calls the API) |
| `apply` | `match(reply, box), slot → box, staged, clr` | ν-join relaying to `box` (its own key) and `staged` |
| `clearNone` | `listEmpty, clr → ready` | ordinary, before the first result |
| `clear` | `list(m), clr → ready` | coloured consumer, drain |
| `show` | `staged(n), ready → list(n), slot` | coloured consumer, relay |

Each query has its own fetch transition, so with an API call that answers asynchronously the two
requests are in flight at once on every executor, whether or not it starts a transition again while
an earlier firing of it is in flight ([CONC-002]), and replies land in `reply` in the order the
actions answer. A stale reply stays in `reply`: `apply` is name-disabled for it once `retire` has
taken its name out of `box`. `box`, `staged`, `list`, `inflightA` and `inflightB` never hold more
than one token (`slot` bounds `staged` and `list`; `idle` and the two keystrokes bound the rest),
so the graph's free choice of a resident name coincides with the executor's FIFO order on them;
only `reply` can hold a stale reply beside the current one. The net is closed: `typed` holds exactly two keystrokes, and the verdicts below are about that net, not
about an unbounded keystroke stream (for one, see "Modelled injection" above). The net rests only
after both keystrokes are consumed (`retire` stays enabled while `typed` and `box` are non-empty),
so the quiescent verdicts speak about markings where all input has been typed and processed. The
results:

- `QuiescentNameAligned(box, list)` is `Proven`: at rest, the list shows the results of the query in
  the box.
- `NameAligned(box, list)` is `Violated` with a shortest witness of 8 firings: after the second
  keystroke the box holds the new name while the list still shows the old results. Only the
  quiescent form holds.
- `QuiescentCount({list}, 1, 1)` ([VER-002]) is `Proven`: at rest, exactly one result is shown.

The buggy variant replaces `apply` with `apply_bug: reply(n), slot → staged, clr`, a coloured
consumer relay with no match on `box` (`box`, `inflightA`, `inflightB`, `reply`, `staged`,
`list` declared carriers, `sendA` and `sendB` declared mints). `QuiescentNameAligned(box, list)`
is `Violated` with a shortest witness of 12 firings in which the reply to the first keystroke is
applied last and the list ends on the old results while `box` holds the new name. Every executor
takes that run when both fetch actions are in flight and `fetchA`'s action answers after
`fetchB`'s: `apply_bug` takes the oldest reply, which is then the reply to the second keystroke. The reported trace is one linearisation of that
run; where it lists both replies resident in `reply`, the executor realises the same firings with
`fetchB` answering first. With actions that complete synchronously the replies arrive in mint order
and the bug does not occur, which is why the verdict is about the net and not about one schedule.

**Acceptance Criteria:**
1. (MUST, where offered) On the search-as-you-type net under EXTENDED, `QuiescentNameAligned(box,
   list)` and `QuiescentCount({list}, 1, 1)` are `Proven` and `NameAligned(box, list)` is
   `Violated` with an 8-firing witness; on the buggy variant `QuiescentNameAligned(box, list)` is
   `Violated` with a 12-firing witness. Every verdict is attributed to Route B.
2. (MUST, where offered) On the same net, a property naming an uncoloured place
   (`QuiescentNameAligned(box, ready)`) or a place absent from the net (`QuiescentNameAligned(box,
   nope)`) is `Unknown` with a reason naming the place, never `Proven`. With two uncoloured places the reason names the first in
   `S`: `QuiescentNameAligned(box, ready, clr)` names `ready`.
3. (MUST, where offered) Under BASE the same net is `Unknown` for `QuiescentNameAligned(box, list)`:
   the coloured set is the match keys `reply` and `box`, `fetchA` and `fetchB` write `reply`
   without being mints, `retire` consumes `box` without a match, and `apply` produces its key
   `box`, so the net is outside the BASE fragment; the reason names EXTENDED and the report names the ignored relay
   declarations ([NU-054] AC5).
4. (MUST, where offered) No route other than Route B, listed above, decides either property: called
   directly, each returns no verdict or `Unknown` with the reason that only Route B decides them,
   and the script encoders return no script; a Route B truncation stays `Unknown` unless the
   prefix rule finds a violation.
5. (MUST, where offered) The predicate is invariant under name permutation: evaluated on a class and
   on that class with its name-symbols permuted, it gives the same answer, and running the
   search-as-you-type net with names minted in another scope ([NU-010]) changes no verdict. It is
   also invariant under reordering `S`.
6. (MUST, where offered) With `typed` registered as an environment place under `AlwaysAvailable`
   (and not in the initial marking), `QuiescentNameAligned(box, list)` is `Unknown` with a reason
   naming `typed`, on the fixed net and on the buggy variant; it is never `Proven`. A call whose
   initial marking holds a token in a coloured place is `Unknown`, with a reason naming the place
   where no earlier refusal of the refusal order applies: on the same net,
   `QuiescentNameAligned(box, list)` with `box` marked names `box`.
7. (MUST, where offered) `S` is a list. On the search-as-you-type net,
   `QuiescentNameAligned(box, staged, list)` and the singleton `NameAligned(list)` are `Proven`;
   `QuiescentNameAligned(box, list, reply)` is `Violated` with a 9-firing witness (a stale reply
   rests in `reply`), and `NameAligned(reply)` with a 6-firing witness (both replies resident). With
   `typed` marked with 3, `QuiescentNameAligned(reply, staged)` is `Violated` with a 12-firing
   witness: the net rests with two stale replies in `reply` and `staged` empty, a marking that
   the cross pair of `reply` and `staged`, without the self pairs, would accept. An empty `S` is rejected at construction, a
   repeated place counts once, at its first occurrence, and the descriptions of one, two and three
   places read as the API notes below give them.
8. (MUST, where offered) Refusals follow the refusal order. On the search-as-you-type net under
   EXTENDED: with `box` marked, `QuiescentNameAligned(box, ready)` names `ready` (an uncoloured
   place before a marked one); with `list` and `inflightB` marked, `QuiescentNameAligned(list, box)`
   names `inflightB` (the marked coloured places in code-point order, not in the order of `S` or of
   the marking); with `typed` registered as in AC6 and `box` marked, `QuiescentNameAligned(box,
   list)` names `typed` (an environment place before a marked coloured place).

**Depends on:** [VER-002], [VER-003], [VER-006], [VER-012], [NU-010], [NU-050], [NU-051], [NU-054]
**Test derivation:** the fixtures of `spec/verification-fixtures/nu-aligned-fixtures.json`, run in
every language: the four search-as-you-type verdicts of AC1, the uncoloured places of AC2, the BASE
run of AC3, the environment and marked-coloured-place runs of AC6, the list verdicts of AC7 and the
refusal-order runs of AC8, each asserting that the report names Route B or, for `Unknown`, that the
reason contains the fixture's `reasonContains`. AC4 by sending the AC1 fixed net to each other
route directly, as an in-module unit test, and by the budget fixture, which must still reach
Route B. AC5 as a unit test on the
predicate (with `S` permuted) and a run with a non-default minting scope. The construction rules and
descriptions of AC7 as unit tests.

**Implementation notes (API):** the properties sit beside `JoinedOrDeadLettered` and
`QuiescentCount`.

- Java: `SmtProperty.nameAligned(first, rest...)` and `SmtProperty.nameAligned(places)` for a
  collection, likewise `quiescentNameAligned`; records `NameAligned(List<Place<?>> places)` and
  `QuiescentNameAligned(List<Place<?>> places)`, whose constructors copy, deduplicate and reject an
  empty list. A new permitted record of the sealed `SmtProperty` breaks exhaustive switches, so it
  ships in a major release.
- TypeScript: `nameAligned(...places)` and `quiescentNameAligned(...places)`, typed to take at
  least one place, members of the `SmtProperty` union with `type: 'name-aligned'` and
  `type: 'quiescent-name-aligned'` and the field `places`.
- Rust: `SmtProperty::NameAligned { places: Vec<String> }` and
  `SmtProperty::QuiescentNameAligned { places }`, with constructors
  `SmtProperty::name_aligned(places)` and `SmtProperty::quiescent_name_aligned(places)` over any
  iterable of names, which panic on an empty one. A new variant of the exhaustive enum is a major
  change.
- Python: `name_aligned(places)` and `quiescent_name_aligned(places)` in `libpetri.verification`,
  over an iterable of places, raising `ValueError` on an empty one, through the Rust verifier, also
  re-exported from `libpetri`, as `joined_or_dead_lettered` and `quiescent_count` are.
- Every language describes them byte for byte on the report's `Property:` line as
  `Name alignment of ` and `Quiescent name alignment of ` followed by the names of the places of
  `S` after deduplication, in order, separated by `, ` except that ` and ` separates the last two:
  `Name alignment of box`, `Name alignment of box and list`, `Name alignment of a, b and c`, and
  `Quiescent name alignment of a, b and c` likewise.

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
- Name alignment ([NU-055]) is the one ν property that compares names rather than
  counting tokens; only Route B decides it, and no other route gives it a verdict.
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
