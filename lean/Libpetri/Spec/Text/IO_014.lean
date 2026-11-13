import Libpetri.Spec.Text

requirement_text IO_014
  id "IO-014"
  title "Output ForwardInput"
  priority MUST
  kind B
  body r#"⟦s1|`ForwardInput(from, to)` is a node of an output spec that, on the timeout outcome, deposits in `to` the tokens a firing consumed from its input place `from`.⟧

⟦s2|*If* a `ForwardInput` node of an output spec is not inside the child of a `Timeout` node, *then* building the transition *shall* fail with⟧

```
output spec of transition '<t>' uses ForwardInput('<from>', '<to>') outside the child of a Timeout node; a forward deposits only on the timeout outcome (IO-014)
```

⟦s3|naming the first such node in the order the spec is written (pre-order, children left to right).⟧ ⟦s4|The check runs when the transition is built, on every construction path, as the check of [IO-011] does.⟧

An implementation whose places carry run-time token types (Java) *may* also fail building a transition that has a `ForwardInput(from, to)` whose `to` place's token type cannot hold the tokens of `from`. It runs that check on each `ForwardInput` in pre-order, right after the check that the node's `from` is an input place (AC3). Without that check, keeping a forwarded token compatible with `to` is the net author's task ([CORE-003]).

⟦s5|*When* a firing ends with the timeout outcome, every `ForwardInput(from, to)` in the `Timeout` child *shall* deposit in `to` one token for each token the firing consumed from `from`, carrying the token's value, in consumption order.⟧

⟦s6|The count *shall* be the consumption count of the input arc on `from` ([IO-007]): 1 for `One`, `n` for `Exactly(n)`, and the whole drained batch for `All` and `AtLeast(m)`.⟧

⟦s7|*If* a firing consumed more than one token from `from`, *then* the forward *shall not* deposit fewer tokens in `to` than the firing consumed; in particular it *shall not* forward only the first consumed token.⟧ Forwarding only the first would silently destroy the remaining consumed tokens on the retry path.

⟦s8|*If* a firing consumed no token from `from`, which a declared input cannot do but a mis-declared spec can, *then* the forward *shall* deposit no token in `to`.⟧

Forwarding is thus multiplicity-preserving, which enables retry patterns without losing tokens. A forward into a relay target of a transition with a match specification is checked like every other token of the timeout outcome: when the timeout outcome fails the relay check of [NU-054], the firing fails and its forwards deposit nothing ([NU-054]).

**What a forwarded token carries.** *When* a `ForwardInput` forwards a consumed token, the token it deposits in `to` *shall* carry the consumed token's `created_at` as well as its value. `ForwardInput` exists so a retry does not lose tokens, and a token's creation time is part of what it keeps: it is provenance across exactly the path a net takes when something went wrong, and the [NU-022] tie-break orders correlation names by it. Forwarding is therefore the one exception to [TIME-015]'s token-stamping rule: a forwarded token is the consumed token itself, not a token the executor mints, so it does not take the injected epoch clock. A *minted* recovery token, such as the unit token of a bare `Place` child, does.

**Acceptance Criteria:**
1. `from` must be a declared input place of the transition (validated at build time).
2. On timeout, one token is produced to `to` for each token consumed from `from`,
   preserving both the original values and their consumption (FIFO) order.
3. Invalid `from` reference → build error.
4. `In.All` or `In.Exactly(n)` on `from` with N tokens consumed → exactly N tokens
   appear in `to`; token count is conserved across the timeout.
5. A forwarded token's `created_at` equals the original's and is **not** re-stamped from the
   epoch clock, while a minted recovery token in the same branch *is*, in every implementation.
6. **Analysis deposits what the executor deposits.** Every analysis that expands output
   branches ([IO-016], [VER-001]) models a timeout forward with the count of AC2: a
   `ForwardInput(from, to)` whose `from` input is `One` or `Exactly(n)` deposits `1` or `n`
   tokens in `to` on the timeout outcome, not one. On `t: exactly(2, a) → xor(c, timeout(50,
   forwardInput(a, b)))` from `{a: 2}`, `PlaceBound(b, 1)` is `Violated` on every route. A
   forward from an `All` / `AtLeast` input deposits the drained batch, a marking-dependent
   count, a transfer: the graph routes, which fire each marking, count it exactly and decide
   the net, while the routes that read the flat net, which no post vector can hold it in,
   refuse it ([VER-001] AC5).

7. A `ForwardInput` outside the child of a `Timeout` node is rejected when the transition is
   built, with the message above: `ForwardInput(a, b)` as the whole spec,
   `Xor(c, ForwardInput(a, b))` and `And(c, Xor(e, ForwardInput(a, b)))`.
   `Timeout(d, ForwardInput(a, b))` and `Xor(c, Timeout(d, And(e, ForwardInput(a, b))))` build.

**Depends on:** [IO-007], [IO-013], [EXEC-010], [TIME-015]
**Test derivation:** Transition with input P1 and ForwardInput(P1, P2) in timeout; action
times out; verify P2 receives the original P1 values. Repeat with `all()` and
`exactly(3)` on P1 over 3 tokens; verify P2 receives all 3 in order. Under an injected clock,
seed P1 with tokens stamped before the run, time the action out, and verify in every language
that the P2 tokens carry the seed stamps while a sibling `Place` recovery token carries the
clock's. The AC6 net verified at enumeration budgets 0 and the default: `Violated`, with a
one-step trace ending at `{b: 2}`. Build a transition with each rejected spec of AC7 and verify
the exact message; build each accepted spec and verify it builds."#
