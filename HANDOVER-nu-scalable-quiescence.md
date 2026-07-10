# Handover: scalable exact ν-net deadlock-freedom (NU-052 done, NU-053 proposed)

Driver: the Marvin **text chat** net is a fork-threaded ν-net (per-turn `freshName` co-minted
into a guard branch and an assistant branch, correlated at a ν-join) with timed dead-letter
drains and heavy independent-branch parallelism. We want a **genuine, machine-checked, scalable
deadlock-freedom ("no-stall" / fast-request non-interference) proof** of it.

Two obstacles were hit and one is solved:

- **Route B (name-aware SCG) explodes.** It decides ν quiescence exactly, but enumerates: the
  text net is **>2,000,000 name-partition classes for a single turn** (independent guard × intent
  × knowledge × assistant × speculative-search interleavings; no partial-order reduction). Truncates
  → `Unknown`.
- **Route A (bounded name-colouring SMT / IC3-PDR) scales but is too narrow.** IC3/PDR flattens the
  same net to **96 places / 100 transitions and runs in ~1.9 s** — no explosion. But `NameColouredEncoder`
  (i) only accepts the strict BASE `mint → matched-join` fragment and (ii) returns `mkFalse()` for
  `DeadlockFree` (comment: *"does not yet model the absence of an enabled transition"*).

So the scalable path exists (IC3/PDR) but the coloured encoder must be extended. That is **NU-053**.

---

## NU-052 — conflict-only priority for Route B  — DONE (this session)

Branch `nu-conflict-priority`, commit `8b63108` (worktree
`/home/db/repositories/libpetri/.claude-wt/nu-conflict-priority`). Java only; **needs Rust port +
TS + Python inherit before landing.**

**Problem.** Route B (`NuScgVerifier`/`NameStateClassGraph`) is priority/timing-blind — it expands
every base-enabled transition. On the dead-letter-drain idiom (an immediate, higher-priority matched
consumer, e.g. a ν-join, vs. a delayed, lower-priority orphan drain over the same coloured place) it
reports a **spurious stall** (the drain stealing a live token) that the eager, priority-ordered
`BitmapNetExecutor` cannot exhibit.

**Fix.** New opt-in `analysis/PrioritySemantics { NONE, CONFLICT }` (default `NONE` = byte-for-byte
unchanged). Under `CONFLICT`, `NameStateClassGraph` does not expand a transition `L` from a class when
another enabled transition `H` has: strictly higher priority; a shared **consumed** input place
(read/inhibitor excluded); `H.timing().earliest() <= L.timing().earliest()`; **and `H` actually fires
in this class** (`willFire` — a match/join must be *name*-enabled, not merely base-enabled; this guard
is essential on a ν-net). Threaded through `NuScgVerifier.verify(..., PrioritySemantics)` and exposed
as `SmtVerifier.prioritySemantics(...)`.

**Soundness.** Removes only interleavings the eager, priority-ordered executor never produces (it fires
ready transitions in descending priority within a pass, so `H` takes the contested token); `L` is not
lost — it re-expands once the conflict is gone. Fixture `NuScgPriorityTest` (4 tests, all green):
NONE reports the spurious stall; CONFLICT proves no-stall via Route B; and — critically — CONFLICT
still finds a **genuine** orphan deadlock (does not over-prune). Full Java suite green (67 reports, 0 fail).

Files: `analysis/PrioritySemantics.java` (new), `analysis/NameStateClassGraph.java`,
`smt/NuScgVerifier.java`, `smt/SmtVerifier.java`, `smt/NuScgPriorityTest.java` (new).

> NU-052 alone does **not** fix the text net — Route B still explodes on it. It's a correctness
> prerequisite (kills the spurious drain-steal stalls) and is independently useful for small ν-nets.

---

## NU-053 — EXTENDED-coloured + quiescence in the SMT/IC3 encoder  — PROPOSED (the real feature)

Goal: make `z3/NameColouredEncoder` (Rust `name_coloured_encoder.rs`) accept the EXTENDED fragment
**and** encode quiescence, so IC3/PDR decides ν `deadlockFree` **soundly and scalably** (k = budget).
Four parts, each soundness-critical. Rust is source of truth; Java/TS port byte-faithfully; Python
inherits.

### Part 1 — EXTENDED fragment (carriers, relays, drains)
Today `buildPlan` sets `coloured = ⋃ matched-join correlated inputs`, and every coloured place must be
produced *only* by a budget-consuming mint and consumed *only* by a matched join (`buildPlan` lines
~200–245). The text net's coloured join keys (`GuardSafe`, `ClassifiedResponse`) are produced by
**relays** (`InputGuard`, `PassClassificationGate`), not mints → rejected.

Port the EXTENDED name-fragment (already in `NameFragment.classify` / `FragmentMode.EXTENDED`) into the
colour domain:
- `coloured = matched-inputs ∪ declared carrierPlaces` (thread `carrierPlaces` into `buildPlan`, mirroring
  `budgetPlaces`).
- New klass `Consume(int colouredIn, int[] colouredOut)` for a non-match transition with **exactly one**
  coloured input at count 1 (relay if `colouredOut` non-empty, drain if empty).
- Encode rule (per colour `c`): `cur[in][c] >= 1  →  in[c]-=1; for each out: out[c]+=1` (mirrors the
  `Join` rule but threads the symbol into coloured outputs instead of only consuming). See
  `NameStateClassGraph.nameSuccessors` `Role.Consume` for the exact reference semantics.
- Co-mint already works (a `Mint` stamps one fresh colour into *all* its coloured outputs).

### Part 2 — Quiescence (`DeadlockFree`)
`encodeViolation(DeadlockFree)` must become `deadlock ∧ ¬atSink` where
`deadlock = ⋀_transitions ¬enabled_c(t)` over the coloured marking (mirror flat `encodeDeadlock`, but
colour-aware, and with the same env-injection relaxation `relaxEnv=true`):
- Untouched: `¬uncolouredEnabled`.
- Mint: `¬uncolouredEnabled ∨ (∀c: ∃ coloured place q with cur[q][c] ≥ 1)` (no globally-fresh colour).
- Join: `¬uncolouredEnabled ∨ (∀c: ∃ input i with cur[i][c] = 0)` (no colour shared by all inputs).
- Consume (relay/drain): `¬uncolouredEnabled ∨ (∀c: cur[in][c] = 0)`.

Extract an `uncolouredEnabled(t)` BoolExpr from `uncolouredIncidence` (currently it pushes the guards
inline). Also route `JoinedOrDeadLettered` here (same shape: pending place non-empty in a quiescent class).

### Part 3 — XOR (remove the 1:1 net↔flat assumption)
`buildPlan` hard-rejects `flat.transitionCount() != net.transitions().size()` (line ~130) and reads
`ft.source().matchSpec()` assuming an ordered 1:1 map. The text net XORs everywhere. Fix: classify each
**flat** transition by its own pre/post incidence (each XOR branch is already a separate flat row with its
own coloured in/out), and take the match spec from the branch's source. Verify the budget/relay discipline
per flat row.

### Part 4 — Budget lifetime (the subtle one)
The coloured encoding needs `≤ k` **live colours** (k = initial budget). The current `buildPlan` proves
that structurally by "budget consumed only by mints, refunded only by joins, refund ≤ min-mint-cost." **The
text net refunds `TURN_BUDGET` at the terminals (`FinalizeMessage`/`SendOutputViolation`/…), not at the
guard join.** The colour's lifetime is fork→join; the budget's is fork→terminal ⊇ fork→join — so
`#live-colours ≤ #held-budget-tokens ≤ k` still holds, but by a different argument the current check can't see.

Two sound options (pick in the libpetri plan):
- **(a) Marvin-side:** add a dedicated *colour-budget* place consumed at `ForkInput` and refunded at every
  transition that **consumes the colour** (the guard join **and** each coloured-token drain:
  `DiscardOnVaCase`, `DiscardStaleResponse`, `DiscardOnViolation`, VA-delegation-send). Then the budget's
  lifetime == the colour's lifetime and the existing discipline applies unchanged. Cleanest for the encoder.
- **(b) Encoder-side:** generalise the conservation check to "no budget-producing transition is reachable
  before the colour is consumed on any path" — needs path/ordering reasoning; harder, but avoids a Marvin
  net change.

### Gate + downgrade
- `SmtVerifier` line ~372: build the coloured plan for `DeadlockFree`/`JoinedOrDeadLettered` too (drop the
  `isReachabilitySafety(property)` restriction once Part 2 lands).
- `applyNuGuard`: do **not** downgrade quiescence when the exact coloured plan was used (`exact == true`) —
  exact colouring does not over-fire, so the downgrade reason (NU-050 #1) no longer applies. Keep the
  name-blind downgrade for the non-coloured fallback.

### Verification plan
- Fixtures (`org.libpetri.smt`): BASE mint→join `deadlockFree` PROVEN; EXTENDED (relay/carrier/drain)
  `deadlockFree` PROVEN and a drain-removed VIOLATED; an XOR fixture; a budget-inflation fixture that must
  fall back (return null → over-approx), never a false PROVEN.
- Differential: Route A coloured `deadlockFree` must agree with Route B (SCG) on every small fixture that
  Route B can close.
- Marvin: `TURN_BUDGET` (Phase-1c re-port) as budget place → `SmtVerifier.forNet(textNet)`
  `.property(deadlockFree()).budgetPlaces(TURN_BUDGET).carrierPlaces(<chain>).fragmentMode(EXTENDED)` →
  genuine `isProven()` via IC3/PDR in seconds.

---

## Marvin application (verified this session, ready to resume once NU-053 ships)

- **Net is in the EXTENDED fragment.** `SmtVerifier.forNet(textNet).fragmentMode(EXTENDED)` classify
  **accepts** the real refactored text net (Route B decides, sound+complete) — proven. Requires the
  `reset(GUARD_SAFE)` removal (a coloured place may carry no reset arc; also a genuine concurrency fix —
  the guard verdict is always consumed within its turn by the join or VA-delegation).
- **Complete carrier chain** (omit any one → a re-mint → join permanently name-disabled → false stall):
  `GUARD_INPUT, ASSISTANT_INPUT, ASSISTANT_DIRECT_INPUT, ASSISTANT_SEARCH_INPUT, OPTIMISTIC_RESPONSE,
  UPDATE_RESPONSE, UNGUARDED_RESPONSE` (`GUARD_SAFE`, `CLASSIFIED_RESPONSE` auto-coloured as match keys).
  The assistant branch hops `ASSISTANT_INPUT →(CheckSpeculativeSearch)→ {ASSISTANT_DIRECT_INPUT |
  ASSISTANT_SEARCH_INPUT} →(AssistantCall[AfterSearch])→ OPTIMISTIC_RESPONSE →(knowledge gate,
  UPDATE_RESPONSE on the changed re-ask)→ UNGUARDED_RESPONSE →(PassClassificationGate)→ CLASSIFIED_RESPONSE`.
- **Budget place:** `TURN_BUDGET` (Phase-1c: consumed at `ForkInput`, refunded at assistant-flow terminals).
  See Part 4 — either re-point its refund to the colour-consuming transitions (option a) or generalise the
  encoder check (option b).
- The guard join `PassInputGuardApprovedModelResponse` matches `CLASSIFIED_RESPONSE.nameId` ×
  `GuardSafe.nameId`; scope the proof to the ν-region by declaring `MODEL_RESPONSE` (its output) a sink.
