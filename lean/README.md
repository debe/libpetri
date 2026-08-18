# `lean/` — machine-checked soundness: verifier abstraction + precompiled hot loop

A Lean 4 development with two axes.

**Axis 1 (original): is the SMT verifier's untimed abstraction actually an
over-approximation of the executor's semantics?** Every false-`Proven` bug in
the project's history — `667e67d`, `a4038f5`, `c23cd9e` (NU-052), `98b9297`
(VER-006), NU-051 — is a case where it was not. That failure mode is the worst
one available: the verifier answering "safe" about an unsafe net.

**Axis 2 (this extension): is the precompiled executor's hot loop correct?**
`PrecompiledBackend` (flat ring-buffer token pool, opcode-stream consumption,
two-level bitmaps) must be observationally identical to the `BitmapBackend`
reference. The development models the flat pool at full fidelity and proves
token conservation ("no missing tokens") plus a per-cycle backend refinement.
The original scope note said engine bugs were "runtime plumbing no proof of the
firing rule can reach" — that remains true of the *async* plumbing (sync-throw
containment, `Out.Timeout` context lifetime, cross-thread `marking()`), but the
backend seam turned out to be exactly provable territory: four real
Bitmap/Precompiled divergences (ready-order tie-break, read-vs-reset ordering,
duplicate-input-place panic, unknown-place token drop) sat in code the
differential suite never reached, and each is retrodicted here.

## Build

```bash
cd lean
lake build                  # a few seconds; no dependencies
```

Toolchain is pinned in `lean-toolchain` (Lean 4.32.2). There is **no Mathlib
dependency**: `α` erases colours to token counts, so every abstract marking is
ℕ-valued and core `Nat`/`List`/`omega` suffice. CI runs `lake build`, a
`sorry`/`admit` grep, and a `#print axioms` check on the headline theorems.

## What is proved

`Libpetri/Soundness.lean` — **Proposition 1**, `α(R(N)) ⊆ R(N̂)`
(`theory/verification-preserving-neural-substitution.typ`, where it is a proof
sketch). `proposition_one` is the reachability statement; `prop1_step` is the
simulation lemma carrying it.

It holds under two side conditions, and **the shipped encoder checks neither**.
Both are shown necessary by a concrete decidable counterexample, so neither is
proof bureaucracy:

### Finding 1 — a consume-all arc must be unguarded — **resolved by removing guards**

`GuardFreeConsumeAll`, witness `guard_hypothesis_is_necessary`.

**Status: discharged.** Input guards have since been deleted from Rust and TypeScript
(they were already absent from Java, and `IO-006` had tombstoned them in 2026-02 —
the implementations were drift from an unfinished breaking change). With no per-arc
predicate left, `GuardFreeConsumeAll` holds vacuously for every net that can now be
built, so Proposition 1 applies unconditionally on this axis and the encoder has
nothing left to be blind to.

The model below is kept deliberately: it is the evidence that motivated the removal,
and the record of what the abstraction could *not* have been made sound against.

`net_flattener.rs` never inspects an input arc's guard, so the encoder emits
`m'_i = post[i]` — place emptied — for every `In::All` / `In::AtLeast` place
(`smt_encoder.rs:165-167`). The executor consumes only guard-*matching* tokens
(`bitmap_backend.rs:590-600`, `count_matching` + `remove_matching`), so
guard-failing tokens survive the firing.

Concretely: place holds `[1, 2]`, guard accepts only `1`. The executor leaves
one token; the abstraction says zero. The abstract successor is *smaller* than
the concrete one, which is how `PlaceBound` gets a false `Proven`.

It was reachable through the documented API in Rust (`all_guarded`) and TypeScript
(`all(place, guard)`), with Python inheriting Rust's. **Java was never affected** —
its `Arc.In` records carried no guard field, because `6558113` had already removed
them there. So this was a two-verifier gap, not three.

### Finding 2 — an action writes at most one token per output place

`UnitOutput`, witness `unit_output_hypothesis_is_necessary`.

`validate_out_spec` (`executor_core/output.rs:37`) is a **set-membership**
check — it verifies *which* places the action wrote to, never how many tokens
it wrote to each. So an action satisfying `Out::Place(p)` may write any number
of tokens to `p`, while `net_flattener.rs:85-88` fixes the abstract gain at one
token per branch place (`all_places` returns a `HashSet`).

Neither paper states this condition. Paper A's Assumption W1 ("observationally
pure with respect to the marking") constrains side channels, not output
multiplicity, so it does not imply it.

## What is proved — axis 2, the precompiled hot loop

`Libpetri/RingArith.lean` + `Libpetri/Ring.lean` — the flat token pool at
full fidelity (`token_pool` + `place_offset`/`ring_head`/`ring_tail`/
`ring_capacity`/`token_counts`, including `grow_ring_static`'s
block-append-and-leak). `Pool.WF` is RB1–RB3 (ring well-formedness, slot
occupancy — what makes `ring_remove_first`'s `.unwrap()` total — and block
disjointness); `Pool.proj` is the refinement map onto per-place FIFO lists
(`materialize_marking`). Every ring primitive carries a WF-preservation and a
projection-effect lemma: `removeFirst` pops the head, `addLast` appends
through the grow path (`growRing_proj_self` = RB5's grow half), `peekFirst` is `head?`, and
`removeMatching_some` is RB6 — both compaction slides remove exactly the
first predicate match and preserve survivor order.

`Libpetri/Compile.lean` + `Libpetri/Conservation.lean` — the compiled consume
program (`compile_consume_ops`, inputs then RESET tail, the
`reset_ops_start` boundary) and its interpreter. **`token_conservation`** is
the headline "no missing tokens" theorem: over one firing, every place's
pre-fire queue is *exactly* `delivered ++ reset-destroyed ++ survivors` as a
list equality — nothing lost, nothing duplicated, order preserved.
`consume_faithful` (IO-007 prefix delivery), `produceAll_spec` (EXEC-020
tail append), and reads-as-`head?` complete the FR group.

`Libpetri/Enablement.lean` — the presence bitmap and the dirty set.
`fireConsume_dirty_sound` is CONC-005's load-bearing fact: any state change
that can flip another transition's enablement marks it dirty, because
`canEnable` reads only touched places, a firing changes only consumption
places, and `affected_transitions` covers every toucher. `disable_frame`
shows the EXEC-003 loser path is sound *without* marking dirty;
`updateEnablement_sync` shows the dirty scan restores exact enablement.

`Libpetri/Refinement.lean` — **`precompiled_refines_bitmap_immediate`**: on
the untimed/immediate fragment (the production fast path), any number of
executor cycles keeps the precompiled backend's materialized marking equal to
the reference backend's `Marking`, with identical firing decisions — actions
abstracted to a pure emission function whose inputs are proven identical
(`inputs_bag_rel` / `reads_bag_rel`), so equal outputs are derived, not
assumed.

`Libpetri/Sched.lean` — the general (timed / multi-priority) ready path with
abstract `Nat` clocks. The canonical order `(priority DESC, enabled_at ASC,
tid ASC)` is a strict total order on distinct tids, so a sorted permutation
of the ready set is *unique* (`eq_of_perm_of_sorted`) — which is why fix
(a)'s `sort_unstable_by` is deterministic — and
`collect_ready_general_refines` forces the post-fix per-level drain
(`LevelBlocks`, RQ1–RQ4) and the reference's stable sort onto the same list.
The full timed-cycle refinement (deadlines, TIME-012 restarts) remains
future work; only the ready-collection phase — where divergence (a) lived —
is covered.

## What is retrodicted

The acceptance criterion for this spike: the model must have enough resolution
to see defects that really happened, not just restate the paper.

`Libpetri/Priority.lean` — **`c23cd9e` (NU-052)**. `PrioritySemantics::Conflict`
*removes* transitions from the analysed relation, so it can only lose behaviour;
Paper A step 4 states priorities are not encoded, so Theorem 2 never covers this
mode. `preFixPrune` (before the `willFire` guard) and `postFixPrune` (shipped)
are separated by `willFire_guard_is_necessary`: a base-enabled but name-disabled
ν join out-competes the orphan drain, so the pre-fix condition prunes a firing
the executor really does perform.

`Libpetri/Retrodict.lean` — **`98b9297` (VER-006)**.
`envless_reach_is_trivial` proves that without the injection rule the reachable
set is exactly `{M₀}`, so `false_proven_without_injection` establishes
`PlaceBound(p₁, 0)` vacuously; `injection_reaches_violation` shows the bound is
violated once `smt_encoder.rs:81-83`'s injection rule is present.

`Libpetri/RetrodictExec.lean` — **the four backend divergences** (pre-fix
commit `1bdf586`), each with a concrete minimal witness:
`tid_order_diverges` (ready order by tid instead of enablement time),
`read_reset_order_diverges` (reads peeked after resets drained),
`canEnable_insufficient_for_totality` (duplicate input arcs pass
`cardinality_check` yet the second `ring_remove_first` unwraps `None`), and
`unknown_place_drop` (pre-fix `produce_token` was the identity for unknown
places — a token lost without trace). None was reachable by the differential
suite before the fixes' new tests.

## Scope

**In:** untimed fragment, all five arc kinds, input cardinalities, XOR
flattening, environment places, conflict-priority pruning; and (axis 2) the
flat ring-buffer pool at full fidelity, the consume opcode program, the
presence/dirty bit machinery, the immediate-fragment backend refinement, and
the general-path ready ordering with abstract `Nat` clocks. Three later
modules extend both axes: `TimedCycle.lean` (a control-cell witness that the
two shipped `enforce_deadlines` diverge observably after a reap —
`deadline_reap_dirty_diverges`; which behaviour TIME-013 should mandate is a
pending semantics decision), `MatchCache.lean` (the ν-match cache lockstep
invariant `match_cache_lockstep` under the fast-path eligibility gate, at
queue-contents granularity, plus per-conjunct necessity witnesses), and
`Strengthening.lean` (P-invariant strengthening preserves the abstract
reachable set under H1/H2/H3′ — the H1 hypothesis forced the consume-all/
reset guard now shipped in all three validators).

**Out:** real-valued time, deadline *refinement* (the reap divergence is
witnessed in `TimedCycle.lean`, but the TIME-013 semantics ruling and the
full timed-cycle refinement remain open — only the ready-collection phase is
covered), DBM / Berthomieu–Diaz state
classes; the async loop and action plumbing (actions are pure
emission functions here); ν-match `best()` selection and tie-break (NU-022
AC2 stays a differential-test claim — `MatchCache.lean` covers queue
contents only); the u64 word packing and two-level summaries (bit/set
granularity only; PERF-042 AC4 pins the words differentially); the u32
opcode encoding (FR4 is proven on the structured op stream); the ν name
layer beyond the boolean `nameEnabled` abstraction in `Priority.lean` (so
the ν-budget retrodictions `667e67d` and `a4038f5` are **not** covered);
Lemma 0 quiescence; extraction to the four implementations. One resolution
lesson: the immediate-fragment refinement idealizes the EXEC-003 recheck the
same way on both sides, which is why pre-fix divergence #5 (same-pass output
visibility in the precompiled recheck; fixed 2026-08, pinned in
`backend_suite_tests.rs`) fell outside the proven correspondence — an
explicit snapshot-recheck model that would have *seen* it is future work.

**Modelling assumptions**, each stated in the source where used:

- At most one input arc per place per transition (`specAt`). The flattener sums
  `required_count` over duplicates; nets with two input arcs on one place are
  outside the model.
- Concrete firing is specified at token-count granularity (`alphaFireC`,
  `StepC`), which is all `α` observes.

## Fidelity

A model that drifts from the encoder proves nothing about the encoder. Every
definition carries a doc comment naming the exact shipped function and line it
models. If one of those functions changes, this development is wrong until the
comment is rechecked — that is the maintenance obligation this directory adds.
The function name is the primary reference and the line number a hint: a moved
line is a doc fix, a changed function is a fidelity breach.

### Fidelity check

That obligation is mechanized. `fidelity.toml` pins every modeled Rust item —
one `[[pin]]` per function (or type, where the type itself is what is modeled)
with the Lean modules that model it — and `fidelity.lock` records a SHA-256 of
each pinned item's current source span, doc comments and attributes included:
a comment edit trips it too, deliberately, because the comments carry the
semantics the model was checked against. `scripts/lean-fidelity-check.py`
re-hashes the pins against the lock, and additionally fails if any `.rs` file
cited in a Lean doc comment has no pin at all — so a new citation forces a new
pin. `RetrodictExec.lean`'s pre-fix citations (commit `1bdf586`) are
historical; they carry no pins of their own beyond the current items they
diverge from.

When the check fails:

1. Open the named Rust function and re-verify the listed Lean module(s)
   against it — fix the model, or confirm the change is outside the modelled
   fragment.
2. Refresh any line-number hints that moved (a moved line is still just a
   doc fix; the pin follows the function by name).
3. `python3 scripts/lean-fidelity-check.py --update` to regenerate the lock.
4. Commit the lock together with any Lean fixes, so the lock always records
   the exact code this development was last verified against.

Nothing in `theory/` is edited by this development; the papers are read-only
reference for the theorem statements.
