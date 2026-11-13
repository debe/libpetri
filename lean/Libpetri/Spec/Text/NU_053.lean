import Libpetri.Spec.Text

requirement_text NU_053
  id "NU-053"
  title "EXTENDED-Coloured Quiescence in the Route A SMT Encoder"
  priority MAY
  kind F
  body r#"[NU-050] Route A encodes a bounded ν-net as `k` colours and decides
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

⟦s1|*When* the coloured encoding decides a quiescence property, it *shall* treat an encoding state as violating exactly when every flat row (each XOR branch is its own row) whose transition is not reapable ([VER-002]) is disabled in the state for an uncoloured reason or, when the row touches a coloured place, for every colour below `k`, and the property's own clause holds of the state's all-colour token counts.⟧

⟦s2|*If* the verifier sets the colour-slot bound to `k`, *then* some covering weighting `y` *shall* have `⌊y·M0⌋ = k`, and no covering weighting *shall* have `⌊y·M0⌋ < k`, a covering weighting being one with `y ≥ 0`, `y_p ≥ 1` on every coloured place and `y·C_t ≤ 0` on every flat transition.⟧

⟦s3|*If* the verifier sets the colour-slot bound to `k`, *then* the exact re-check *shall* have accepted a weighting and given it the bound `k`.⟧

⟦s4|The exact re-check *shall* accept a weighting `y` exactly when `y ≥ 0`, `y_p ≥ 1` on every coloured place, `y·C_t ≤ 0` on every flat transition and `⌊y·M0⌋ ≤ 2^31 − 1`, and *shall* give an accepted weighting the bound `⌊y·M0⌋`.⟧

The update of a coloured consumer, per colour `c`, emits `(- x 1)` for its input column
and `(+ x 1)` for each coloured output column. A consumer that relays into its own
input (a self-loop, `spin: a, tick → a, tock` with `a` coloured) gets **no** update term
for that column: it keeps its `>= 1` guard and is carried over unchanged, as a join's
key that is also a relay target is ([NU-054]). A rule updates each column once, so
emitting both terms would keep only the `(+ x 1)` and leave the consumer unable to fire
under any law that weights `a`.

⟦s5|*When* the coloured encoding emits the rule of a coloured consumer for a colour `c` below `k`, the rule *shall* be enabled only when colour `c` of the input holds a token, and *shall* subtract one from colour `c` of the input, add one to colour `c` of each coloured output, and leave unchanged colour `c` of a place that is both the input and an output and every other colour column.⟧

⟦s6|The verifier routes a bounded quiescence query to Route B first; when Route B
truncates (`Unknown`), it **defers** to this scalable Route A encoding rather
than returning `Unknown`.⟧ ⟦s7|A verdict from the coloured plan is not downgraded as a
name-blind verdict would be (the colour-aware deadlock does not over-fire joins); only the
`Ignore` downgrade of [VER-006] applies to it.⟧ Its `Proven` is sound while the
declared mints and the coloured consumers keep their contracts ([NU-010], [NU-051]);
the report prints the colour-slot bound as `colour-slot bound k=<k>`, after the
`Colour-slot bound:` line below, and names the transitions whose contracts it assumes.

⟦s8|The verifier *shall not* run Route B ([VER-012]) after the colour-slot bound in one verification call.⟧

⟦s9|*When* the verifier runs the colour-slot bound for a `DeadlockFree`, `TerminatesAtSink`, `JoinedOrDeadLettered` or `QuiescentCount` property, it *shall* have run Route B ([VER-012]) in the same verification call.⟧

⟦s10|The verifier *shall not* run the colour-slot bound on a net without a ν-join or without a declared budget place, or when environment injection is modelled or an arrival feeds a coloured place ([VER-006]).⟧

⟦s11|*When* Route B builds its name-partition graph for a `DeadlockFree`, `TerminatesAtSink`, `JoinedOrDeadLettered` or `QuiescentCount` property of a ν-net with a declared budget place and the graph returns `Unknown`, the verifier *shall not* return that `Unknown` from Route B and *shall* hand the query over to the next phase of the dispatch.⟧

⟦s12|*When* the verifier has built the coloured plan and the call is not under `Ignore` with environment places registered, the fixpoint query *shall* decide with the verdict of the coloured query and *shall not* downgrade it.⟧

⟦s13|*When* the verifier has not built the coloured plan for a `DeadlockFree`, `TerminatesAtSink`, `JoinedOrDeadLettered` or `QuiescentCount` property of a ν-net with a ν-join, the fixpoint query *shall not* return `Proven`.⟧

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

⟦s14|*When* the verifier solves the colour-slot program of a flat net with `n` places and `m` transitions that has a covering weighting `y` with `⌊y·M0⌋ ≤ 2^31 − 1`, and `n ≤ 4096`, `m ≤ 16384`, `C(n+m, n)·(2n+1)·(n+m+1) ≤ 4000000` and `(n+1)!·E^(n+1) ≤ 2^63 − 1`, where `E` is the largest of 1, every initial count and `n` times every `pre + post` of a flat transition at a place, it *shall* set a colour-slot bound unless the solve is stopped ([VER-013]).⟧

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
from one budget token has `k = 0`; a reset arc on the uncoloured budget keeps the plan."#
