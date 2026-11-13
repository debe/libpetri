import Libpetri.Spec.Text

requirement_text VER_012
  id "VER-012"
  title "Name-Aware State Class Graph (ν-Partition Quotient)"
  priority MAY
  kind F
  body r#"The state class graph ([VER-010]) MAY be made **ν-aware** to decide [NU-020] join
correlation *exactly* — the [NU-050] **Route B** carve-out. Each correlation
token carries an abstract, interchangeable name-symbol; a matched (ν-join)
transition is enabled only when one symbol is shared by every correlated input
(not merely when the token counts allow); a minting fork introduces a
globally-fresh symbol; and the graph is quotiented under name-permutation
symmetry (its dedup key abstracts the symbol identities). The timed firing domain
([VER-011]) is carried beside the name partition, with a matched join's clock gated by
name-enablement ([NU-050]) and, unless `assumeNoReaping` is set, without latest bounds
([TIME-013]); the Route B class key pairs the base class (for a timed net its marking, zone
and earliest-ready times) with the canonical key of the name layer. Quiescence ([NU-050]) is
decided over the name-aware terminal classes.

⟦s1|*When* the Route B graph fires a ν-join on a name-symbol, every correlated input *shall* hold at
least the required count of that symbol, and the firing *shall* remove the required count of that
symbol from each correlated input and add one token of it to each relay target of the fired branch
([NU-054]).⟧ ⟦s2|*If* every correlated input of a ν-join holds at least the required count of a
name-symbol, *then* the name successors of a firing of that join *shall* include one with the
canonical key of the join fired on that symbol.⟧ ⟦s3|*When* the Route B graph fires a coloured consumer
([NU-051]), it *shall* fire it on a name-symbol its coloured input holds, removing one token of that
symbol from the input and adding one token of it to each coloured output of the fired branch.⟧ ⟦s4|*If*
the coloured input of a coloured consumer holds a name-symbol, *then* the name successors of a
firing of that consumer *shall* include one with the canonical key of the consumer fired on that
symbol.⟧ ⟦s5|*When* the Route B graph fires a minting transition, its one name successor *shall* add one
token of a name-symbol that no coloured place of the class holds to each coloured output of the
fired branch.⟧ ⟦s6|*When* the Route B graph fires a transition that neither mints, joins nor consumes a
name-symbol, its one name successor *shall* be the name layer of the class unchanged.⟧ ⟦s7|Two name
layers *shall* have the same canonical key exactly when one is the other with its name-symbols
renamed by a permutation.⟧ ⟦s8|The Route B graph *shall* identify two classes exactly when they have the
same base class and their name layers have the same canonical key.⟧ ⟦s9|*When* the Route B graph fires a
transition, the successor *shall* hold on each place the transition does not reset the tokens the
place held, less the tokens the transition's input on that place consumes by [IO-007] (all of them
for an `All` or `AtLeast` input), plus the tokens the fired branch deposits there.⟧

The executor fires a ν-join on one of the names that enable it ([NU-020]); the graph fires it on
each of them, up to renaming, and a coloured consumer ([NU-051]) on each resident name. Route B's
successor step gives any two classes with the same key the same transition labels and successor
keys, up to order, so the premise of the completeness sentence below holds for it.

⟦s10|Every class the Route B build stores *shall* be reachable in the graph from the initial class,
whether the build closed, was truncated, was stopped or stopped early.⟧ ⟦s11|*If* the Route B build
closes, *then* it *shall* have expanded every class it stored.⟧ ⟦s12|*While* the graph's successor step
gives any two classes with the same key the same transition labels and successor keys, up to order,
*if* the Route B build closes, *then* it *shall* have stored a class with the key of every class the
graph reaches from the initial class.⟧ ⟦s13|*If* the Route B build stops early at a violating class of a
reachability-safety property, *then* its verdict for that property *shall* be the verdict of the
same build without the early stop, unless that build is stopped by the total budget or a
cancellation.⟧ ⟦s14|*If* the Route B build stops early, *then* it *shall not* report the graph as closed.⟧

**Acceptance Criteria:**
1. A ν-join fires in the graph only on a name shared by all correlated inputs; a
   marking reachable only by equating two distinct names is *not* reachable
   (NU-050 #1), with no budget place required.
2. Two markings differing only by a permutation of name-symbols are the same
   state class (the quotient is finite when the live-name pool is structurally
   bounded).
3. **Conditional on an executor-faithful consumption model** (see below): when the
   graph closes within the class bound the verdict for reachability-safety and quiescence is
   sound for every executor run ([NU-050]) and complete for the free-choice name semantics the
   graph explores: every class the graph reaches is stored and expanded, so a property that a
   class the graph reaches violates is `Violated`, and a `Violated` names a class the graph
   reaches. When that graph keeps a latest
   bound (under `assumeNoReaping`, or a direct call on a timed net) it reads each firing as one
   instant step, so the verdict is exact only for an on-time executor whose actions take no
   time, and the report says so ([VER-004] AC3). A graph that does not close within the class
   bound truncates (NU-050 #2 — undecidability
   surfaces as truncation) and the shared predicate runs over the explored prefix by the rule
   of [VER-017] ("Verdicts from a truncated graph"): a safety property violated by any stored
   class, or a quiescence property violated by an **expanded** class with no successor, is
   `Violated` with the shortest witness in the explored graph and a report line naming the
   truncation; otherwise the verdict is `Unknown`. A truncated graph never yields `Proven`, and a
   reachability-safety `Unknown` from Route B is still final (the dispatcher has no fallback for
   it), so the prefix check is what turns a shallow violation into a verdict. PNID Fig. 11(b)
   (`research/net-metrics/validation/pnid/`), `placeBound(order_clerk, 2)` at a class bound of
   50: `Violated` with the depth-3 trace `create_order ×3`.
4. `All` and `AtLeast(m)` inputs drain their place in the graph exactly as they do at
   run time: after a successor step the source place holds no residue, so an inhibitor
   arc on that place is satisfied in the successor class.
5. **Early stop for safety properties.** For a reachability-safety property (`PlaceBound`,
   `BranchPlaceBound`, `Unreachable` and `MutualExclusion`, the safety set of [VER-017]'s
   "Verdicts from a truncated graph", and `NameAligned` of [NU-055]) the build checks each class
   with the same shared predicate as it is discovered and stops at the first violating class. BFS discovers classes in index
   order, so that class is the lowest-index violating class — the one the check over a full or
   truncated graph selects — and its path is the shortest; verdict and route are
   identical to a build without the early stop and the witness ends at the same class; only the
   class count, the time and, among equally short paths to that class, the path the witness
   takes may differ. When
   the stop comes before the class bound, the report note
   `Note: Route B stopped at the first violating class after N classes (VER-012). Every explored class is reachable and classes are discovered breadth-first, so the counterexample is a real firing sequence and a shortest one to any violation.`
   replaces both the truncation note and the exact-graph note, and the parent whose expansion
   discovered the violating class does not count as expanded; when the bound is hit first, criterion 3 applies unchanged. Quiescence
   properties do not stop early (they need expanded classes). An early-stopped graph is not
   complete and MUST NOT be treated as closed. PNID Fig. 11(b), `placeBound(order_clerk, 2)` at
   the default class bound: `Violated` with `create_order ×3` after a handful of classes,
   where it took 1.8 s to fill the cap first.

**Exactness precondition (consumption model).** The soundness and completeness of
criterion 3 are not unconditional: they hold only while the graph's successor relation
removes as many tokens from each place as the executor would. The successor step MUST
derive each input's token count from the canonical `consumptionCount(available)` of
[IO-007] (so `All` and `AtLeast(m)` consume **all** available tokens, not merely
`requiredCount()`). Which names the removed tokens carry is the graph's free choice, where
the executor takes the oldest ([EXEC-010], [NU-020]), so criterion 3 claims completeness only
for the graph's own name semantics. A successor relation that consumes a *minimum* instead leaves phantom residue in
the source place; that residue keeps inhibitor arcs on the place unsatisfied and
suppresses successor classes, so a genuinely reachable marking is reported unreachable —
an **unsound** `Proven`, not a conservative one. Implementations therefore MUST delegate
to the same cardinality contract the executor uses rather than restating it.

**Implementation notes:**
- Rust: Full implementation (`libpetri-verification` `name_state_class_graph` /
  `nu_scg_verifier`); the canonical name-partition key format is shared verbatim.
- Java: Full implementation (`org.libpetri.analysis.NameStateClassGraph` /
  `org.libpetri.smt.NuScgVerifier`).
- TypeScript: Full implementation (`verification/analysis/name-state-class-graph`
  / `verification/nu-scg-verifier`).
- Python: inherits the Rust analysis through `verify`.
- Memory: an implementation MAY intern (hash-cons) the base class and the name layer
  between state classes. The base intern key MUST include the class-relative
  earliest-ready times alongside the marking and zone, because the [NU-052] prune reads
  them while class equality does not. Class identity MUST carry them too: the graph's
  dedup key is the pair of intern ids (base, name layer), not the class object, so two
  arrivals that agree on marking, zone and name layer but disagree on the earliest-ready
  times stay two classes and each keeps its own prune input. Interning is semantics-free by key-equivariance of
  the successor step (Lean `Interning.lean`, `interned_keys_eq`): the reachable quotient
  and the verdict are unchanged; class indices and the reported counterexample trace may
  differ from a non-interned build.
- Successor emission (orbit dedup): a join yields one successor per **distinct signature**
  among its enabling symbols, not one per symbol; a symbol's signature is its count vector over
  the coloured places in `colouredOrder`, and the consume role ([NU-051]) is deduplicated the same
  way. Two symbols with equal signatures are exchanged by a transposition that fixes the name
  marking, so their successors have equal canonical keys: the class set and the set of
  (label, key) successor pairs are unchanged, and only parallel identical edges disappear. The
  per-symbol emission copied and keyed every successor only to collapse them into one class,
  which made join-heavy graphs roughly quadratic in their class count. Measured in TypeScript on
  PNID Fig. 11(b): 8 000 classes in 0.49 s instead of 14.5 s; 100 000 classes in about 19 s
  instead of an estimated 35 min. Class counts and verdicts are unchanged, and so is the discovery
  order when each signature is represented by its first enabling symbol; a count of edges is not a
  stable quantity to test. The renaming-equivariance that Lean `Interning.lean`
  assumes per role still holds, because the number of distinct signatures is itself invariant
  under renaming.
- Early stop (AC5) is Route B only: the [VER-017] enumeration and the [VER-023] timed check still
  build their graphs in full, since those feed the state-space cache and other properties. An
  early-stopped build is a BFS prefix, so every class in it is reachable, by the argument of Lean `build_reach` for the enumeration
  route.
- The counterexample path is read from per-class labelled successor lists, not by scanning every
  edge for each dequeued class.
- Solver-free (no Z3); the verifier prefers Route A's bounded name-colouring for
  budget-declared untimed reachability-safety and uses this route for quiescence,
  budget-less, and timed ν-nets.

**Depends on:** [VER-010], [VER-011], [VER-017], [NU-020], [NU-050], [IO-007]

**Test derivation:** Two independent mints feeding one join with no budget place;
verify the join output is unreachable (NU-050 #1); a same-mint variant reaches it;
an ever-minting net truncates to `Unknown`. For AC3's prefix rule, PNID Fig. 11(b) under
`placeBound(order_clerk, 2)` at a class bound of 50 is `Violated` with a depth-3 trace, and a
quiescence property on an ever-minting net whose only successor-free classes are frontier classes
stays `Unknown`. For the early stop (AC5), the same Fig. 11(b) query at the default class bound
is `Violated` after fewer than 50 classes with the trace `create_order ×3`, a quiescence property
on that net explores as before, and on several fixtures the early-stop witness ends at the class the
witness from a build without it ends at. For the orbit dedup, the class count of every existing Route B fixture is
unchanged, and an 8 000-class build of Fig. 11(b) finishes under a generous time bound."#
