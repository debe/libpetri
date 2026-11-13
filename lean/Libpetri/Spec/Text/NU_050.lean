import Libpetri.Spec.Text

requirement_text NU_050
  id "NU-050"
  title "Exact Verification of Matched Transitions"
  priority MAY
  kind B
  body r#"The untimed encoder is value-blind ([VER-004]). For ν-nets this is
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
  equates two different names. ⟦s1|It stays in linear arithmetic, and its `Proven` is
  sound while the declared mints and the coloured consumers keep their contracts
  ([NU-010], [NU-051]).⟧ It applies to the **mint → matched-join fragment**: coloured
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

⟦s2|*If* the build of the Route B graph is stopped, because it runs out of total budget or is cancelled ([VER-013]), *then* Route B *shall* answer `Unknown`, whatever classes the build stored.⟧

⟦s3|*If* the build is not stopped and a stored class violates a safety property, or an expanded class at which the net rests violates a quiescence property, *then* Route B *shall* answer `Violated`, also when the graph does not close.⟧

⟦s4|*If* Route B answers `Violated`, *then* the class its counterexample ends at *shall* violate the property: a stored class for a safety property, an expanded class at which the net rests for a quiescence property.⟧

⟦s5|*If* the build is not stopped and no class violates the property, *then* Route B *shall* answer `Proven` when the graph closes and `Unknown` when it does not.⟧

*If* the Route B graph does not close, *then* Route B *shall not* answer `Proven`.

Under modelled injection ([VER-006]) Route B treats an environment place as an inexhaustible
input and so cannot observe its count or the names injected into it; it declines (`Unknown`)
when a verdict would depend on them ([VER-006] AC8).

On a timed net Route B gives a matched join a clock only while one name-symbol is present in
every correlated input, because the executor enables the join only then ([NU-020]). A join whose
inputs hold tokens but share no name has no clock, so its latest bound constrains no other
firing. The clock-restart rule of [TIME-012] reads the name layer too: a firing after which no
name is present in every correlated input restarts the join's clock, even when the inputs still
hold tokens, and a join whose inputs come to share a name starts a fresh clock then. ⟦s6|This holds with
and without the latest-bound relaxation for a late executor ([TIME-013]).⟧

⟦s7|*While* a transition is not enabled with an eligible name ([NU-020], [NU-022]), Route B *shall* hold no clock for it, even when its inputs hold the tokens its arcs require but no name is present in every correlated input.⟧

⟦s8|*When* a transition fires and another transition `j` holds a clock and is not enabled with an eligible name ([NU-020], [NU-022]) in the intermediate marking ([TIME-012]), Route B *shall* take `j`'s clock away, even when `j`'s inputs still hold tokens, and *shall* give `j` a fresh clock if the firing leaves `j` enabled with an eligible name.⟧

⟦s9|*When* a transition fires and another transition `j` holds a clock and is enabled with an eligible name ([NU-020], [NU-022]) before the firing, in the intermediate marking and after the firing, Route B *shall* keep `j`'s clock.⟧

⟦s10|*When* a firing leaves a transition `j` enabled with an eligible name ([NU-020], [NU-022]) and `j` held no clock before it, Route B *shall* start `j`'s clock at that firing.⟧

⟦s11|*When* a transition fires, Route B *shall* take its clock away and *shall* give it a fresh clock if the firing leaves it enabled with an eligible name ([NU-020], [NU-022]).⟧

⟦s12|*While* time passes, Route B *shall* keep the marking and the start of the clock of every transition enabled with an eligible name ([NU-020], [NU-022]), and *shall* advance the clock reading by the time that passed.⟧

⟦s13|Route B *shall* fire a transition only when it holds a clock that has run for at least the transition's earliest bound ([TIME-001]), and *shall* leave the clock reading unchanged at a firing.⟧

⟦s14|Route B reads every coloured token through one name.⟧ ⟦s15|It assumes that each key and relay
projection reading a coloured place returns the name its writer put there: the name a mint
stamped, or the name a relay or consumer carried over.⟧ The analysis cannot inspect a projection,
so this is a contract on the net, like the mint contract of [NU-010]. Two projections that read
one place differently, or a projection that returns no name for a written token, fall outside
it.

⟦s16|Both routes read a coloured write as a fresh name only for a declared mint ([NU-010]), and as
the consumed name only for a coloured consumer ([NU-051]).⟧ A write the executor makes on timeout
is read by what it is: a forward carries the consumed token's name and a unit token has none.
Where no role reads a coloured write faithfully, the net is outside both routes.

**Soundness.** Both routes are sound against the untimed executor, with no environment place,
while the projections and the actions keep the contracts above.

⟦s17|*If* the coloured places start empty, every transition is in the fragment for its role, every key and relay projection reads the name its writer put there, and every declared mint and coloured consumer keeps its contract ([NU-010], [NU-051]), *then* Route B *shall* answer `Proven` for a safety property only if no marking the untimed executor reaches violates it.⟧

⟦s18|*If* in addition every correlated input takes at least one token, *then* Route B *shall* answer `Proven` for a quiescence property only if no marking the untimed executor reaches and rests at violates it.⟧

⟦s19|*If* Route A builds its plan with the colour-slot bound of [NU-053], every key and relay projection reads the name its writer put there, and every declared mint and coloured consumer keeps its contract, *then* a `Proven` of the coloured encoding of a safety property *shall* hold of every marking the untimed executor reaches.⟧

⟦s20|*If* in addition no transition of the net is reapable, *then* a `Proven` of the coloured encoding of a quiescence property *shall* hold of every marking the untimed executor reaches and rests at.⟧

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
name-colouring) eliminates it, while a same-name join still reaches its merge."#
