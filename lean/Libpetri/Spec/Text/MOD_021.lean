import Libpetri.Spec.Text

requirement_text MOD_021
  id "MOD-021"
  title "Channel Composition (transition merge: arc union + conflict resolution)"
  priority MUST
  kind B
  body r#"When a composition binding maps an interface channel to a caller-side `Transition`, the two transitions are **merged** into a single transition in the composed net. The merged transition combines:

1. **Arcs**: the union of all input, output, inhibitor, read, and reset arcs from both sides, with same-place arcs reconciled per the deduplication rule below.
2. **Timing** (per [TIME-001]): when one side's timing is `Immediate`, the merged timing is the other side's timing, so two `Immediate` sides give `Immediate`. Two equal timings collapse to that timing. ⟦s1|Any other pair, two different timings neither of which is `Immediate`, MUST be rejected with an error naming the caller-side transition.⟧ ⟦s2|That error MUST also name both timings, unless the two sides also break rule (d) below, in which case an implementation MAY report the rule (d) error instead.⟧ The merged timing is therefore always one of the two sides' timings.
3. ⟦s3|**Priority**: the merged transition has the caller-side transition's priority; the instance-side priority is ignored.⟧
4. **Action**: composed sequentially: caller-side action first, then instance-side action. The composed action is exposed to the executor as a single atomic firing: the executor sees one transition per [CORE-021].
5. **Identity**: the merged transition's name is the caller-side transition's name; the instance-side renamed channel transition is NOT separately added to the enclosing builder.

**Arc deduplication rule** (for clause 1): for every pair of arcs from the two sides targeting the same `Place` (by identity per [CORE-002]):
- ⟦s4|(a) **Same arc type without a cardinality** (`Read`, `Inhibitor`, `Reset`): a same-place pair collapses to a single arc.⟧
- (b) **Same arc type with a defined merge**: `Input` arcs on one place are reconciled by the canonical merge table below, not by rule (a). Output is one spec tree per transition rather than a per-place arc: the two sides' trees combine under a single outer `And` (clause 1), and a one-sided spec carries through unchanged. ⟦s5|For example, when each side produces into `Q`, the merged `And(Q, Q)` names `Q` twice in one branch, which the transition builder rejects ([IO-011]), so the channel merge is rejected.⟧
- ⟦s6|(c) **Same arc type with no defined merge**: an `Input` pairing absent from the table MUST be rejected at compose time with the diagnostic below.⟧
- ⟦s7|(d) **Different arc types**: when both sides have arcs on one place and the two sides' sets of arc types on it (input, inhibitor, read, reset; an output is not counted) differ, for example an `Input` arc on `P` on one side and a `Reset` arc on `P` on the other, or `Read` + `Reset` on one side and `Read` alone on the other, the merge MUST be rejected at compose time. When the timings merge (clause 2), at most one side carries a ν-net match ([NU-060]) and the declared-place correspondences merge ([MOD-031]), the error MUST name the caller-side transition, such a place and each side's set of arc types on it, each set written as its arc-type names (`inhibitor`, `input`, `read`, `reset`) in alphabetical order, separated by a comma and a space, in square brackets, for example `[input]` or `[read, reset]`. Two sides declaring the *same* set of arc types on a place (e.g. `Read` + `Reset` on each side) are not a conflict: their same-type arcs pair up under rules (a)/(b).⟧

**Canonical input-arc merge table.** This is the single normative statement of rule (b); [MOD-061] and [CORE-030] refer here rather than restating it. The table is symmetric.

| Left | Right | Merged |
|------|-------|--------|
| `one` | `one` | `exactly(2)` |
| `one` | `exactly(n)` | `exactly(n + 1)` |
| `exactly(n)` | `exactly(m)` | `exactly(n + m)` |
| `all` | `all` | `all` (idempotent collapse) |
| `atLeast(n)` | `atLeast(m)` | `atLeast(max(n, m))` |
| anything else | | **rejected** per rule (c) |

`one`/`exactly` sum because each side's demand is an independent fixed draw. `atLeast` does not sum: both sides take every available token, so the merged arc only has to carry the stricter minimum. `all` does not sum either: each side drains the place, so two `all` arcs merge to one `all` arc.

⟦s8|*When* two input arcs on one place are merged and each of them is `one` or `exactly`, the merged arc *shall* be `exactly` of the sum of their counts, where `one` counts 1.⟧

⟦s9|*When* two `all` input arcs on one place are merged, the merged arc *shall* be `all`.⟧

⟦s10|*When* two `atLeast` input arcs on one place are merged, the merged arc *shall* be `atLeast` of the larger of their two minimums.⟧

⟦s11|*If* two input arcs on one place are merged and the pair is none of these three cases (each side `one` or `exactly`, both `all`, both `atLeast`), *then* the merge *shall* be rejected (rule (c)).⟧

⟦s12|A rejection MUST name the seam, both cardinalities, and the place, in this shape:⟧

```
<seam>: input arcs <a> and <b> collide on place '<p>' and have no additive merge (MOD-021 rule (c)). Use a single arc with exactly(n) / atLeast(n).
```

`<seam>` is `Fusion set '<name>'` ([MOD-061]) or `Channel composition '<name>'`; `<a>` and `<b>` render cardinality only (`one()`, `exactly(3)`, `all()`, `atLeast(2)`) with no place name embedded. Method spelling follows the host language (`at_least(n)` in Rust and Python).

The result is one merged `Transition` in the flat net; firing it consumes/produces tokens per the unioned arc set in a single atomic step per [EXEC-001].

In the sentences below, a *channel merge* merges a caller-side transition with the instance-side channel transition it is bound to, whose arcs the port bindings have already rewritten ([MOD-020]). ⟦s13|The sentences cover a caller-side transition whose name is neither empty nor made of white space only, that was not added to the net builder before the compose call and that has no arc on a port bound in the same compose call; for other caller-side transitions the implementations differ, and this requirement does not yet state the outcome.⟧

⟦s14|*When* a channel merge succeeds, the merged transition *shall* have the caller-side transition's name and priority.⟧

⟦s15|*When* a channel merge succeeds and neither side has two input arcs on one place, the merged transition *shall* have at most one input arc on each place: none where neither side has an input arc, an arc of the one side's cardinality where only one side has an input arc, and an arc of the cardinality the canonical input-arc merge table gives for the two where both sides have one.⟧

⟦s16|*When* a channel merge succeeds, the merged transition *shall* have, for each of the arc types inhibitor, read and reset, one arc of that type on every place on which either side has an arc of that type, and no other arc of that type.⟧

⟦s17|*When* a channel merge succeeds, the output specification of the merged transition *shall* be `And` of the caller-side specification and the instance-side specification, in that order, when both sides have one, the one side's specification when only one side has one, and none when neither side has one.⟧

⟦s18|*When* a channel merge succeeds, the timing of the merged transition *shall* be the instance-side timing when the caller-side timing is `Immediate`, and the caller-side timing otherwise.⟧

⟦s19|*When* a channel merge succeeds, the action of the merged transition *shall* be the caller-side action followed by the instance-side action.⟧

⟦s20|*When* a channel merge succeeds, the merged transition *shall* pass the checks of the transition builder ([CORE-030], [IO-011], [IO-012], [EXEC-012]).⟧

⟦s21|*If* neither side's timing is `Immediate` and the two timings differ, *then* the channel merge *shall* be rejected with a message that names the caller-side transition.⟧

⟦s22|*If* neither side's timing is `Immediate`, the two timings differ, and the two sides' sets of arc types agree on every place on which both sides have an input, inhibitor, read or reset arc, *then* the channel merge *shall* be rejected with a message that names the caller-side transition and both timings.⟧

⟦s23|*If* both sides have an input, inhibitor, read or reset arc on one place and the two sides' sets of arc types on that place differ, *then* the channel merge *shall* be rejected.⟧

⟦s24|*If* the timings merge, at most one side carries a ν-net match ([NU-060]), the declared-place correspondences merge ([MOD-031]), and on some place both sides have an input, inhibitor, read or reset arc and the two sides' sets of arc types on it differ, *then* the channel merge *shall* be rejected with a message that names the caller-side transition, one such place and the two sides' sets of arc types on it, each set written as in rule (d).⟧

⟦s25|*If* the timings merge, at most one side carries a ν-net match ([NU-060]), the declared-place correspondences merge ([MOD-031]), the two sides' sets of arc types agree on every place on which both sides have an input, inhibitor, read or reset arc, neither side has two input arcs on one place, and both sides have an input arc on a place for which the canonical input-arc merge table has no merge, *then* the channel merge *shall* be rejected with the rule (c) diagnostic for such a place and its two arcs, the caller-side arc first, with the seam `Channel composition '<name>'` where `<name>` is the caller-side transition's name.⟧

⟦s26|*When* the timings merge, at most one side carries a ν-net match ([NU-060]), the declared-place correspondences merge ([MOD-031]), the two sides' sets of arc types agree on every place on which both sides have an input, inhibitor, read or reset arc, neither side has two input arcs on one place, every place where both sides have an input arc has a merge in the canonical input-arc merge table, and the transition builder accepts every transition that these sentences allow as the merged transition, the channel merge *shall* succeed.⟧

**Acceptance Criteria:**
1. Bind a caller transition `T` (with arcs `[in: P]`, `out: Q`, `Immediate`, priority 0) to a channel transition `C` (with arcs `[in: R]`, `out: S`, `Immediate`, priority 0). The composed net contains one transition with input arcs from both `P` and `R`, output arcs to both `Q` and `S`, `Immediate` timing.
2. Bind two transitions with different non-`Immediate` timings, for example `Delayed(100ms)` and `Deadline(50ms)`; verify the compose call is rejected with a message identifying both timings.
3. Bind a caller transition with `Immediate` timing to a channel transition with `Delayed(100ms)`; verify the merged timing is `Delayed(100ms)`. Bind two transitions that are both `Window(10, 100)`; verify the merged timing is `Window(10, 100)`. Bind caller `Deadline(100ms)` to instance `Delayed(50ms)`; verify the compose call is rejected.
4. The merged transition's action runs the caller-side action then the instance-side action sequentially within one firing; observable token movement is atomic from the executor's perspective.
5. After build and run, the executor invokes the merged transition once per fire (not twice).
6. **Arc deduplication, merge table:** bind a caller transition with `Input(One) -> P` to a channel transition with `Input(One) -> P` on the same caller place `P`; verify the merged transition has a single `Input(Exactly(2)) -> P` arc. Verify the remaining rows too: `All` + `All` collapses to `All`, and `AtLeast(1)` + `AtLeast(3)` merges to `AtLeast(3)` (not `AtLeast(4)`).
7. **Arc deduplication, different types are rejected:** bind a caller transition with `Input -> P` to a channel transition with `Reset -> P`; verify the compose call is rejected with a message naming the caller-side transition, `P`, `[input]` and `[reset]`.
8. **Arc deduplication, off-table pairings are rejected:** bind a caller transition with `Input(One) -> P` to a channel transition with `Input(All) -> P`; verify the compose call is rejected with the diagnostic shape above, naming the seam, both cardinalities, and the place.
9. **Token timestamp on merged production:** when the merged transition fires and produces a token to a place that is itself a port-merge or fusion target, the produced token is stamped as any token the executor creates is ([CORE-011]) and deposited at the tail of its place as the tokens of any admitted completion are ([EXEC-020], [CONC-003]). Tokens that distinct firings of one or more merged transitions produce into one place keep the order in which the executor admits the completions of those firings ([CONC-003]). The merged transition emits a single `TokenAdded` event per produced token (cf. EVT-011), not one per side of the merge.

**Depends on:** [MOD-005], [MOD-020], [MOD-031], [CORE-011], [CORE-021], [CORE-030], [TIME-001], [IO-011], [IO-012], [EXEC-001], [EXEC-012], [EXEC-020], [CONC-003], [NU-060]
**Test derivation:** Compose two transitions with non-overlapping arcs; verify the resulting flat net has one transition combining all arcs. Compose with two different non-`Immediate` timings; verify rejection. Compose an `Immediate` side with a timed side; verify the merged timing is the timed side's. Compose with two `one` or `exactly` input arcs on the same place; verify the counts are summed. Compose with two `atLeast` input arcs on the same place; verify the larger minimum is kept. Compose with `one` and `all` input arcs on the same place; verify rejection. Compose with conflicting arc types on the same place; verify rejection."#
