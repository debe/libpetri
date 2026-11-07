# Glossary: firing semantics

This glossary fixes the terms the CORE and IO firing requirements use. It is not numbered and
defines no requirements; each entry cites the requirements that define the term. The Lean
counterpart is `lean/Libpetri/Spec/Glossary.lean`, whose docstrings quote these entries.

---

### Place

A named container that holds tokens [CORE-001]. Two places are the same place exactly when they
have the same identity [CORE-002].

### Token count

The number of tokens a place holds in a marking, written `m(p)`. Enablement and firing read
token counts only: no input arc tests a token's value [IO-006].

### Marking

The distribution of tokens across all places at one instant [CORE-070]. A place no arc touches
keeps its tokens and is inert [CORE-072].

### Marked

A place is marked when its token count is not zero.

### Input arc

An arc from a place to a transition that the transition consumes from when it fires, according
to the arc's cardinality `One`, `Exactly(n)`, `All` or `AtLeast(m)` [CORE-030], [IO-001]–[IO-004].
A transition declares at most one input arc per place [CORE-030].

### Required count

`requiredCount()`: the fewest tokens an input place must hold for the transition to be enabled.
It is 1 for `One` and `All`, `n` for `Exactly(n)` and `m` for `AtLeast(m)` [IO-007].

### Consumption count

`consumptionCount(available)`: the tokens a firing removes from an input place that holds
`available` tokens. It is 1 for `One`, `n` for `Exactly(n)` and `available` for `All` and
`AtLeast(m)` [IO-007].

### Output arc

An arc from a transition to a place: a place that the transition's output spec names
[CORE-035], [IO-017].

### Inhibitor arc

An arc from a place to a transition that disables the transition while the place is marked
[CORE-031]. It never consumes.

### Read arc

An arc from a place to a transition that requires the place to be marked for the transition to
be enabled [CORE-032]. It never consumes.

### Reset arc

An arc from a place to a transition that removes every token from the place when the transition
fires [CORE-034]. It never affects enablement.

### Enabled

A transition is enabled in a marking when every input place holds at least its required count,
every read place is marked and no inhibitor place is marked [CORE-022], [IO-005]. Reset arcs
and output arcs play no part.

### Fire

To fire is to perform one firing. One firing of an enabled transition consumes from its input
places, empties its reset places and deposits the tokens of one outcome [CORE-030], [CORE-034],
[CORE-035]. Read as one step from a marking `m` to a marking `m'`, a firing ignores timing and
priority.

### Consume

To remove tokens from an input place when the transition fires: as many as the consumption
count, oldest first [CORE-030], [IO-007]. Read arcs and inhibitor arcs never consume
[CORE-031], [CORE-032].

### Deposit

The tokens a firing adds to the marking, counted per place: how many tokens each place
receives. It may be written as a list of places with repetition, a place receiving one token per
occurrence, but only the count per place is normative: two deposits that put the same number of
tokens in every place are the same deposit, whatever their order [CORE-036]. A reset place ends a
firing holding exactly what the firing deposited there [CORE-034].

### Output spec

The tree of `Place`, `And`, `Xor`, `Timeout` and `ForwardInput` nodes that says where a
transition's action may write [IO-010]–[IO-014]. A transition with no output spec deposits
nothing.

### Output branch

One way the action can satisfy the output spec: a set of places, taking one child at every
`Xor` and the union at every `And` [IO-015], [IO-016]. With output validation enabled
[CONC-026], a firing that ends with its action deposits one or more tokens in each place of one
output branch and none in any other place: the branch fixes which places receive tokens, not how
many [IO-015], [CORE-036]. The output branches of a spec that builds are pairwise distinct sets
[IO-012]. The analyses that enumerate them model one token per place [IO-016].

### Produced set

The places that received at least one token from a firing [IO-015].

### Timeout outcome

The way a firing ends when the executor's own budget timer on the `Timeout` node fires before
the action completes [IO-013]. An output spec holds at most one `Timeout` node, so a transition
has at most one timeout outcome [IO-013]. The `Timeout` child holds no `Xor` node, so that
outcome deposits in one fixed set of places [IO-013]. The marking then receives the `Timeout`
child's tokens and nothing else: one minted token in each place the child names through `Place`, and for each
`ForwardInput(from, to)` the tokens the firing consumed from `from`, each keeping its value and
`created_at` [IO-014]. It is compared with other deposits per place [CORE-036], [IO-012]. An
exception the action raises is not a timeout outcome.

### Forward

`ForwardInput(from, to)`, allowed only inside the child of a `Timeout` node: on the timeout
outcome, one token in `to` for each token the firing consumed from `from`, in consumption order,
each keeping the consumed token's value and `created_at` [IO-014]. In an output branch it claims
`to` [IO-015].

### Same set of places

Two lists of places name the same set of places when every place of each is a place of the
other, whatever the order or repetition. Places are the same under the implementation's own
`Place` equality [CORE-002], [MOD-024]. Output branches are compared this way [IO-012],
[IO-015].

### Build-time checks

The checks building a transition runs: the input-arc check of [CORE-030], then, on its output
spec and in this order, a place named twice in one output branch [IO-011], more than one
`Timeout` node [IO-013], an `Xor` node inside the child of the `Timeout` node [IO-013], a
`ForwardInput` outside the child of a `Timeout` node [IO-014], a
`ForwardInput` whose `from` is not an input place [IO-014], and two output branches that claim
the same set of places [IO-012]. The first check that fails names the error. No executor option
skips them [CONC-026].

### Builds

A transition builds when it passes every build-time check. A definition that fails one is not a
transition of any net: no executor holds it, so it is never enabled and never fires [CORE-022].
