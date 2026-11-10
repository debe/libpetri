# Glossary: firing semantics

This glossary fixes the terms the CORE and IO firing requirements, the TIME timing
requirements, the EXEC execution requirements, the CONC enablement-check requirements, the ν
verifier requirements and the verifier's bounded runs use. It is not numbered and defines no
requirements; each entry cites the requirements that define the term. The Lean counterpart is
`lean/Libpetri/Spec/Glossary.lean` for the firing terms, `lean/Libpetri/Spec/GlossaryTime.lean`
for the timing terms, `lean/Libpetri/Spec/GlossaryQueue.lean` for the execution terms,
`lean/Libpetri/Spec/GlossaryEnable.lean` for the enablement-check terms and
`lean/Libpetri/Spec/GlossaryNuVer.lean` for the ν verification terms, whose docstrings quote
these entries.

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
be enabled [CORE-032]. It never consumes. A transition has no read arc on a place it has an input arc on
[EXEC-012].

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

The checks building a transition runs: the input-arc check of [CORE-030], the input-count checks
of [IO-002] and [IO-004], the input-and-read check of [EXEC-012], the timing check of [TIME-001],
then, on its output spec and in this order, a place named twice in one output branch [IO-011], more than one
`Timeout` node [IO-013], an `Xor` node inside the child of the `Timeout` node [IO-013], a
`ForwardInput` outside the child of a `Timeout` node [IO-014], a
`ForwardInput` whose `from` is not an input place [IO-014], and two output branches that claim
the same set of places [IO-012]. The first check that fails names the error. No executor option
skips them [CONC-026].

### Builds

A transition builds when it passes every build-time check. A definition that fails one is not a
transition of any net: no executor holds it, so it is never enabled and never fires [CORE-022].

---

## Timing

### Timing

The interval `[earliest, latest]` a transition's timing specification gives: `Immediate`,
`Deadline(by)`, `Delayed(after)`, `Window(earliest, latest)` or `Exact(at)` [TIME-001]–[TIME-006].
`Immediate` and `Delayed` have no finite latest bound; their `latest()` is the maximum duration.

### Maximum duration

The finite stand-in for "no latest bound", about 100 years: `MAX_DURATION_MS` = 3153600000000 ms,
or `MAX_DURATION` in Java [TIME-001]. No valid timing has an earliest bound above it, no valid
`Deadline` has a `by` above it, and no valid `Window` has a latest bound above it [TIME-001].

### Firing clock

The monotonic time source from which the executor stamps armed transitions and computes elapsed
time [TIME-010], [TIME-015]. Its readings never decrease and may repeat [TIME-015].

### Arc place

A place on which a transition has an input, read, inhibitor or reset arc [CORE-030]–[CORE-034].
A place the transition only deposits into is not one of its arc places.

### Write

A firing writes a place when it consumes from it, deposits into it or drains it through a reset
arc. Draining a reset place that is already empty counts as a write. An injected token writes the
place it lands in [ENV-003]. Reading through a read arc and testing through an inhibitor arc
never write [TIME-013].

### Armed

A transition is armed when it is enabled and holds a clock: a stamp, the firing-clock reading
taken by the enablement update that most recently newly armed it [TIME-010]. A transition is newly armed when it is
enabled in the initial marking, when it is enabled after a firing or an injected token that wrote
one of its arc places while it was not armed, and when its clock restarts [TIME-012]. A
transition that is not enabled is not armed. Armed is not Enabled: a reaped transition is enabled
but not armed [TIME-013].

### Elapsed time

The current reading of the firing clock minus an armed transition's stamp [TIME-010]. Only an
armed transition has one.

### Ready

A transition is ready when it is armed, its elapsed time is at least its earliest bound and it is
not expired [TIME-010], [EXEC-002].

### Deadline tolerance

The per-executor grace band added to a latest bound before a transition is reaped: 5 ms by
default, and `0` for strict enforcement [TIME-013].

### Reapable

A transition is reapable when its timing is `Deadline` or `Window` [TIME-013]. `Exact`,
`Immediate` and `Delayed` are not reapable, though `Exact` has a deadline in the sense of
`hasDeadline()` [TIME-001], [TIME-006].

### Expired

A reapable transition is expired when it is armed and its elapsed time is strictly greater than
its latest bound plus the deadline tolerance [TIME-013].

### Reaped

To reap an expired transition is to disarm it in the deadline step of a cycle without firing it,
emitting `TransitionTimedOut` [TIME-013], [EXEC-001], [EVT-009]. A reaped transition keeps its
tokens and stays enabled but not armed, and does not fire, until a firing or an injected token
writes one of its arc places; it is then newly armed if it is enabled [TIME-013].

---

## Execution

### Queue order

The tokens of a place are kept in the order they were added. The oldest token is the head of the
place; a firing consumes from the head, except on a correlated input of a ν-net match [EXEC-010],
[NU-020], and reads the head [EXEC-012], and a deposit adds at the tail [EXEC-020].

### Unknown place

A place the net does not declare: no transition of the net has an arc on it or names it in its
output spec. Its tokens are retained in the marking, inert, since no arc can reference them
[CORE-072].

### Admitted completion

A completion is an action that returned normally [EXEC-020]. The executor admits it when it
processes it, in step 1 of a cycle or, for a synchronous action, inside the firing pass
[EXEC-001]. It never admits the completion of a firing that ended with its timeout outcome
[EXEC-022], that a stop on a terminal place abandoned [EXEC-042] or that an immediate
termination abandoned [ENV-015]. Only an admitted completion deposits, and only when output
validation, if enabled [CONC-026], does not reject its produced set [EXEC-020], [EXEC-021].

---

## Verification

### Injection step

A step of the verifier's flat step relation that adds one token to an injected environment place
that resolves in the flat net: the injection rule of the HORN encoding [VER-006], the
`inject(<place>)` step of the counterexample replay [VER-003] and of the bounded witness phase
[VER-025]. Under `Bounded(k)` it is enabled only while the place holds fewer than `k` tokens,
under `AlwaysAvailable` always. Under `Ignore` and `Arrivals` the flat net has none [VER-006].

### Irredundant run

A run to a violating marking from which no single step can be dropped so that the rest still
replays to a violating marking [VER-025]. An irredundant run need not be a shortest one. The
bounded witness phase reports one that also ends at the first violating marking it reaches.

---

## Enablement check

### Presence bitmap

The bitmap of a marking with one bit per place, set exactly when the place is marked [CONC-004].

### Word

A machine word of a bitmap: it holds the bits of a run of consecutive place indices. A bitmap is
a sequence of words, and a word past the end of a bitmap reads as zero [CONC-004], [PERF-042].

### Needs-mask

The bitmap of a transition with a bit set for each of its input places and read places: all of
them must be marked [CONC-004].

### Inhibitor-mask

The bitmap of a transition with a bit set for each of its inhibitor places: none of them may be
marked [CONC-004].

### Presence check

Phase 1 of the enablement check. It passes on a bitmap when every bit of the transition's
needs-mask is set and no bit of its inhibitor-mask is set:
`(marking & needs-mask) == needs-mask AND (marking & inhibitor-mask) == 0` [CONC-004],
[CONC-008]. Reset arcs and output arcs play no part.

### Cardinality check

Phase 2 of the enablement check. It passes when every input place holds at least its required
count [CONC-008], [IO-007].

### Enablement check

The check an executor runs to decide whether a transition is enabled: the presence check on the
presence bitmap of the marking, then the cardinality check, then, for a transition with a match
specification, the ν-match check [CONC-008], [NU-020].

---

## ν verification

### Coloured place

A place whose tokens carry a correlation name in the name layer of Route B: a match key of a
matched transition [NU-020] and, under EXTENDED, also a declared carrier place [NU-051] and a
relay target [NU-054]. Under BASE the coloured set is the match keys alone [NU-055]. The
classifier computes the coloured set for each call.

### Fragment classifier

The function a ν verifier applies to each transition of a net, in the fragment mode BASE or
EXTENDED, to give it a role in the fragment Route B decides exactly (a mint, a matched join, a
coloured consumer or an ordinary transition), or no role, in which case the net falls back to the
sound over-approximation [NU-050], [NU-051].

### Pre-empt

Under conflict-only priority, a transition H pre-empts a transition L in a class when H is
enabled, is not L, has strictly higher priority, is ready no later than L, has no firing in
flight, fires in the class and competes with L for a consumed input. L is then not expanded from
the class [NU-052].

### Name-aligned

A list S of places is name-aligned in a marking when the places of S together hold at most one
distinct name: any two names resident in places of S, in the same place or in two, are equal
[NU-055].

### Verdict

The answer a verifier gives for a property: `Proven`, `Violated` or `Unknown` [VER-003].
