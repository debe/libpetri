import Libpetri.Spec.Text

requirement_text VER_024
  id "VER-024"
  title "Stubborn-Set Reduction of the Enumeration Route"
  priority SHOULD
  kind B
  body r#"The enumeration of [VER-017] explores every interleaving. A net that forks one token into `k`
independent subnets therefore has a state space close to the **product** of the subnets' spaces,
although each subnet closes alone in a few hundred classes. Measured on a 134-transition composed
agent net that forks into six independent subnets (3 to 404 classes each): about 3 000 000
classes explored in 600 s without closing. A quiescence property only asks about the classes
where nothing is enabled, and the order in which independent transitions fire does not change
which dead markings are reachable. On such a property the route SHOULD therefore expand, at each
class, only the enabled transitions of a **stubborn set** (Valmari's deadlock-preserving
reduction), which brings the graph close to the **sum** of the subnets' spaces.

**When the reduction applies.** All of:

1. The enumeration route of [VER-017] runs (no ν-join, no environment places, untimed, positive
   class budget).
2. The property is a **quiescence property**: `deadlockFree`, `terminatesAtSink`,
   `joinedOrDeadLettered` or `quiescentCount`. Each reads only the classes without successors.
   Safety properties keep the full graph; their violations need not be dead.
3. The net has no drained forward ([IO-014]); its marking-dependent deposits are outside the
   model the reduction is proven on.
4. The reduction is enabled. It is on by default; `partialOrderReduction(false)` turns it off.

**Footprints.** The reduction reads the net the graph is built on (after the inert-place,
in-flight split of [VER-004] and terminal rewrites of [EXEC-042]). For a transition `t`, taking
every outcome of every branch ([VER-021]) together:

- `tests(t)`: its input, read and inhibitor places.
- `writes(t)`: its input and reset places and every place an outcome deposits into.
- `overwrites(t)`: its reset places and its consume-all inputs (`all`, `atLeast`), whose new count
  does not depend on the old one.

Two transitions `t ≠ u` are **dependent** when `writes(t) ∩ tests(u)`, `writes(u) ∩ tests(t)`,
`overwrites(t) ∩ writes(u)` or `overwrites(u) ∩ writes(t)` is non-empty. Independent transitions
enabled together stay enabled after either fires, and firing them in either order reaches the same
marking. A transition that can **increase** `p` is one with an outcome depositing into `p`; one that
can **decrease** `p` has `p` among its inputs or resets.

**The stubborn set at a class with marking `M`.** For a seed transition `s` enabled at `M`, the
closure `S(s)` is the least set containing `s` such that, for every `t ∈ S(s)`:

- (D1) if `t` is enabled at `M`, every transition dependent with `t` is in `S(s)`;
- (D2) if `t` is disabled at `M`, take its **first unsatisfied condition**, over its input and
  read places in code-point order of place name, then over its inhibitor places in code-point
  order: an input or read place `p` with too few tokens
  puts every transition that can increase `p` into `S(s)`; a marked inhibitor place `p` puts every
  transition that can decrease `p` into `S(s)`.

The route computes `S(s)` for every enabled seed and keeps the one with the **fewest enabled
transitions**, the code-point-smallest seed name breaking ties, and expands only that set's enabled
transitions, each with all of its outcomes. The choice is a function of the marking and the net,
so every implementation builds the same reduced graph, with the same class count.

**What the verdict means.** Unchanged: exact for the quiescence property. Every class of the
reduced graph is reachable, and every dead marking reachable in the full graph is reachable in the
reduced one: a run to a dead marking must fire a transition of the set (an enabled member that no
transition outside it can disable would otherwise still be enabled at the end), and the first such
firing commutes to the front. A class has no reduced successor exactly when nothing is enabled at
it, so the classes the reduced graph reports quiescent are exactly the reachable dead markings.
A `violated` is a real firing sequence and stays confirmed ([VER-017] AC2), but it is the shortest
path **in the reduced graph**, which may be longer than the shortest run of the net. A truncated
reduced graph is read as in [VER-017]: a violation in its expanded prefix stands, and no truncated
graph yields `Proven`.

**State-space cache.** A reduced graph answers only quiescence properties, so the cache of
[VER-017] keys it apart from the full graph of the same net and marking: a safety query never
reads a reduced entry, and a quiescence query with the reduction off never reads one either.

⟦s1|*While* the enumeration route of [VER-017] runs on a quiescence property (`deadlockFree`, `terminatesAtSink`, `joinedOrDeadLettered` or `quiescentCount`), on a net without a drained forward ([IO-014]), with the reduction enabled, the route *shall* build the reduced graph.⟧

⟦s2|*If* the property is not a quiescence property, the net has a drained forward or the reduction is disabled, *then* the route *shall* build the full graph of [VER-017].⟧

⟦s3|Every implementation *shall* turn the reduction on by default.⟧

⟦s4|*While* the reduction applies, *when* the route expands a class whose marking `M` enables a transition, it *shall* expand exactly the enabled transitions of `S(s)` for the enabled seed `s` whose closure has the fewest enabled transitions, the code-point-smallest seed name breaking ties.⟧

⟦s5|*When* a transition `t` of `S(s)` is disabled at `M`, the closure *shall* read its first unsatisfied condition over its input and read places in code-point order of place name, then over its inhibitor places in code-point order.⟧

⟦s6|*While* the reduction applies, the route *shall* expand the transitions it selects at a class in ascending code-point order of transition name.⟧

⟦s7|*When* the route expands a class, it *shall* expand only enabled transitions, each with all of its outcomes.⟧

⟦s8|*While* the reduction applies, every dead marking reachable from the initial marking *shall* be reachable by a run that fires, at each class, one of the transitions the route expands there.⟧

⟦s9|*While* the reduction applies, a class *shall* have no reduced successor exactly when no transition is enabled at its marking.⟧

⟦s10|The cache of [VER-017] *shall* key a reduced graph apart from the full graph of the same net and initial marking, so that a safety query, and a quiescence query with the reduction off, never read a reduced entry.⟧

**Acceptance Criteria:**
1. On every net and quiescence property of the conformance corpus, the verdict with the reduction
   equals the verdict without it, and every `violated` trace replays.
2. A net that forks one token into `k` independent cycles of length `n` closes in at most
   `1 + k·n` classes with the reduction and `1 + n^k` without it, with the same verdict.
3. A safety property builds the full graph whatever the setting, with the same verdict, witness
   and class count as before.
4. With `partialOrderReduction(false)` the graph, the witness and the class count are those of
   [VER-017].
5. The class count of a reduced graph is the same in every implementation.
6. When the reduction ran, the report contains the line `Stubborn-set reduction (VER-024): on`
   beside the class count of [VER-017] AC1; its indentation is not fixed.

**Implementation notes:**
- TypeScript: `verification/analysis/stubborn-sets`; `SmtVerifier.partialOrderReduction(enabled)`.
- Java: `org.libpetri.analysis.StubbornSets`; `SmtVerifier.partialOrderReduction(boolean)`.
- Rust: `libpetri-verification` `stubborn_sets`; `SmtVerifier::partial_order_reduction(bool)`.
- Python: `verify(..., partial_order_reduction=True)`.

**Depends on:** [VER-004], [VER-017], [VER-021], [EXEC-042], [IO-014]

**Test derivation:** `fork: start → s0_0 … s(k-1)_0`, and per subnet a cycle
`s(i)_j → s(i)_(j+1 mod n)`. `deadlockFree` is proven with `1 + n` classes reduced (every seed's
set has one enabled transition, so the tie-break keeps advancing the first subnet) against
`1 + n^k` full. Replacing each cycle by a chain ending in `s(i)_n` makes the end
marking dead: `deadlockFree` is violated with a trace of `1 + k·n` firings in both modes, and with
every `s(i)_n` a sink it is proven. A reset arc on a place another subnet deposits into makes the
two subnets dependent, so the reduction keeps both orders."#
