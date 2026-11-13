import Libpetri.Spec.Text

requirement_text NU_020
  id "NU-020"
  title "Match Specification"
  priority MUST
  kind B
  body r#"A transition MAY declare a **match specification**: a subset of its **input**
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

⟦s1|*If* a match builder is given fewer than two keys, *then* building the match *shall* fail.⟧

⟦s2|*If* a match specification keys one place twice, *then* building the match *shall* fail.⟧

⟦s3|Building a match from two or more keys on distinct places *shall* succeed.⟧

⟦s4|*If* a transition fails to build without its match specification, *then* building it with the match specification *shall* fail.⟧

⟦s5|*If* the match specification of a transition keys one place twice, *then* building the transition *shall* fail.⟧

⟦s6|*If* the match specification of a transition keys a place that is not an input place of the transition, *then* building the transition *shall* fail.⟧

⟦s7|Building a transition with a match specification *shall* succeed when the transition builds without the match, the match keys distinct input places of the transition, and the match declares each relay target once and as an output place of the transition ([NU-054]).⟧

**Enablement and the chosen name.**

⟦s8|*When* a transition with a match specification fires, it *shall* be enabled on its token counts ([CORE-022]).⟧

⟦s9|*When* a transition with a match specification fires, every correlated input *shall* hold at least one token of the chosen name and at least its required count of tokens of that name.⟧

⟦s10|*When* a transition with a match specification fires, no other name of which every correlated input holds at least its required count of tokens *shall* have an earlier earliest `createdAt` among its tokens in the correlated inputs than the chosen name, or the same and precede it in the name order.⟧

**Firing.**

⟦s11|*When* a transition with a match specification fires, its action *shall* receive from each correlated input the first tokens of the chosen name in queue order, as many as the consumption count of the input arc with `available` the number of tokens of the chosen name in the place ([IO-007]).⟧

⟦s12|*When* a transition with a match specification fires, each correlated input that is not one of its reset places *shall* end the firing holding the tokens it did not deliver, in their order, followed by the tokens the firing deposited there.⟧

⟦s13|*When* a transition with a match specification fires, its deposit *shall* be one its output spec offers for the tokens the firing takes ([IO-013], [IO-015]).⟧

⟦s14|*When* a transition with a match specification fires, its read arcs *shall* deliver the head of each read place after the inputs are taken ([EXEC-012]).⟧

⟦s15|*When* a transition with a match specification fires, each of its reset places *shall* end the firing holding only the tokens the firing deposited there ([CORE-034]).⟧

⟦s16|*When* a transition with a match specification fires, each place that is not a correlated input *shall* deliver to its action, and keep, the tokens it would without the match specification: the tokens at the head of its queue, as many as the consumption count of its input arc and none without one, and, unless it is a reset place, the rest of its queue in order followed by the tokens the firing deposited there ([EXEC-010], [EXEC-020]).⟧

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
language."#
