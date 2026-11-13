import Libpetri.Spec.Text

requirement_text NU_054
  id "NU-054"
  title "Join Relay"
  priority MAY
  kind F
  body r#"A matched join ([NU-020]) consumes a name and, in the analysed fragment, may not write a name
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

⟦s1|*If* the match specification of a transition declares one place as a relay target twice, *then* building the transition *shall* fail.⟧

⟦s2|*If* the match specification of a transition declares as a relay target a place that its output spec does not name, *then* building the transition *shall* fail.⟧

⟦s3|*When* the match specification of a transition declares one of its own match keys as a relay target and the transition passes every other build-time check, building the transition *shall* succeed.⟧

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

⟦s4|*While* output validation is on, *when* a transition with a match specification fires, no token the firing deposits into one of its relay targets *shall* have a name other than the chosen name under that relay target's key projection, whichever output branch or timeout outcome deposited it.⟧

⟦s5|*While* output validation is on, *when* a transition with a match specification fires, every token the firing deposits into one of its relay targets *shall* have a name under that relay target's key projection, whichever output branch or timeout outcome deposited it.⟧

⟦s6|*While* output validation is on, *if* the output the action of a transition with a match specification returns, or the timeout outcome of its firing, puts into one of the transition's relay targets a token that has no name, or a name other than the chosen name, under that relay target's key projection, *then* the executor *shall* fail the firing with a TransitionFailed event ([EVT-008]) and *shall* deposit none of the tokens of that output or outcome.⟧

⟦s7|*When* the executor fails a firing of a transition with a match specification, it *shall not* deposit any token of the firing's output or timeout outcome, *shall not* restore the tokens the firing consumed, and *shall not* withdraw a batch the action flushed before the firing failed ([IO-015]), whether the executor has already deposited that batch or still holds it queued ([EXEC-021], [CONC-003]).⟧

⟦s8|*While* output validation is on, *if* a batch that the action of a transition with a match specification publishes before it completes ([IO-015]) puts into one of the transition's relay targets a token that has no name, or a name other than the chosen name, under that relay target's key projection, *then* the executor *shall not* deposit that batch, *shall* fail the firing, and *shall* deposit neither the output the action returns nor the timeout outcome of the firing.⟧

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

⟦s9|*While* the fragment mode is BASE, the fragment classifier *shall* give no role to a matched transition that writes a coloured place in any of its outcomes, whatever relay targets it declares.⟧

⟦s10|*While* the fragment mode is EXTENDED, the fragment classifier *shall* give no role to a matched transition that writes, in any of its outcomes, a coloured place it does not declare as a relay target.⟧

⟦s11|*If* the timeout outcome of a matched transition writes a coloured place by anything other than a forward of one of its match keys, *then* the fragment classifier *shall* give it no role, in both BASE and EXTENDED.⟧

⟦s12|*While* the fragment mode is EXTENDED, *if* a matched transition has no reset, read or inhibitor arc on a coloured place, puts on each branch exactly one token, and never a drained batch, into each coloured place the branch writes, writes coloured places only among its relay targets, consumes coloured places only through its match keys, consumes each match key at a fixed count (`One` or `Exactly`), and on timeout writes a coloured place only by forwarding one of its match keys, *then* the fragment classifier *shall* give it the join role with the relay targets it declares.⟧

⟦s13|*While* the fragment mode is EXTENDED, *when* the fragment classifier gives a matched transition the join role, the role *shall* carry as relay targets exactly the relay targets the transition declares.⟧

⟦s14|*While* the fragment mode is BASE, *when* the fragment classifier gives a matched transition the join role, the role *shall* carry no relay targets.⟧

⟦s15|*While* the fragment mode is BASE, the fragment classifier *shall* give a matched transition the role it gives the same transition without relay targets.⟧

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

**Depends on:** [NU-020], [NU-030], [NU-051], [NU-053], [VER-012], [IO-015], [IO-016], [CONC-026]"#
