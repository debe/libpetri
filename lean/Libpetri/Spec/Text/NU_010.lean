import Libpetri.Spec.Text

requirement_text NU_010
  id "NU-010"
  title "Fresh-Name Minting"
  priority MUST
  kind B
  body r#"A transition action MAY mint a fresh name via the action context
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

⟦s1|*When* an action calls `freshName()`, the executor *shall* return a name that differs from every name it returned earlier in the same execution, whether the earlier call came in the same firing or in an earlier one.⟧

⟦s2|For a fixed scope and a fixed sequence of calling transitions, the executor *shall* return the same sequence of names to the `freshName()` calls, whichever firings the calls fall in.⟧

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
token, which has no name. ⟦s3|A declared mint that is not a transition of the net MUST be refused, by a
failure or an `Unknown`, with the same reason naming it at every entry point (verification, script encoding
([VER-013]) and open-net verification ([VER-022])): `declared mint transition 'x' not in the
net (NU-010)`, or `declared mint transitions 'a', 'b' not in the net (NU-010)` when several
are not, each named once in code-point order.⟧ ⟦s4|A refusal that does not depend on the
declaration, such as a stop before the call starts ([VER-013]) or an unresolved property
place ([VER-003]), may come first, and that refusal is then the answer.⟧ Java throws where the mint is declared, the open-net hook
included. TypeScript throws where it is declared on a verifier, and open-net verification
answers `Unknown`. Rust answers `Unknown` from verification and open-net verification before
any route runs, and its script encoding panics; Python raises `ValueError` from script
encoding. The report
of a verdict from either route names the transitions whose mint contract it assumes. When
Route B declines a net only because a transition writes a coloured place without consuming
one and is not declared, the report names that transition and points at the declaration.

⟦s5|*When* a declared mint that has no input arc on a coloured place fires, every name it writes into a coloured place *shall* be a name it minted with `freshName()` in that firing.⟧

⟦s6|*When* a declared mint that has no input arc on a coloured place fires, every name it writes into coloured places *shall* be one and the same name, whether in one place or in several.⟧

⟦s7|The fragment classifier ([NU-051]) *shall* give the mint role only to a declared mint.⟧

⟦s8|*If* a transition without a match specification has no input arc on a coloured place, writes a coloured place and is not a declared mint, *then* the fragment classifier *shall* give it no role.⟧

⟦s9|*If* the timeout outcome of a transition writes a coloured place, *then* the fragment classifier *shall not* give it the mint role.⟧

⟦s10|*If* a transition without a match specification has no input arc on a coloured place and its timeout outcome writes a coloured place, *then* the fragment classifier *shall* give it no role.⟧

⟦s11|The fragment classifier *shall not* give the mint role to a transition that has a match specification or an input arc on a coloured place.⟧

⟦s12|*If* a declared mint has no match specification, no input arc on a coloured place and no reset, read or inhibitor arc on a coloured place, puts on each branch exactly one token, and never a drained batch, into each coloured place the branch writes, writes a coloured place in some outcome and on timeout writes no coloured place, *then* the fragment classifier *shall* give it the mint role, in both BASE and EXTENDED.⟧

⟦s13|*If* a name given to the verifier as a mint transition is not a transition of the net, *then* verification, script encoding and open-net verification *shall* each refuse the request, by failing or by answering `Unknown`, and *shall not* answer `Proven` or `Violated` or return scripts.⟧

⟦s14|*If* a name given to the verifier as a mint transition is not a transition of the net, *then* the reason of that refusal *shall* be `declared mint transition 'x' not in the net (NU-010)`, or `declared mint transitions 'a', 'b' not in the net (NU-010)` when several are not, naming each such name once and in code-point order, unless the same request with no mint transition named gets the same refusal.⟧

⟦s15|*If* every name given to the verifier as a mint transition is a transition of the net, *then* verification, script encoding and open-net verification *shall not* refuse the request with the reason `declared mint transition 'x' not in the net (NU-010)` or `declared mint transitions 'a', 'b' not in the net (NU-010)`, whatever names it gives, unless the same request with no mint transition named gets the same refusal.⟧

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
downstream join and each pair merges (see `nu_fork_mints_unique_ids_then_join_merges`)."#
