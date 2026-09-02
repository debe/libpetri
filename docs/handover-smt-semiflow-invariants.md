# Handover: semiflow-strengthened IC3 (and two smaller ν-net findings)

Branch `scg-memory` in this repo (worktree `/home/db/repositories/libpetri-wt-scg-memory`),
Java only, `pom.xml` at `3.0.2-SNAPSHOT` for local testing. Found while proving a 110-place /
129-transition ν-net (Marvin's text chat net) in `nucleus_marvin`, branch
`text-net-deadlock-freedom`, test `TextCriticalRouteSafetyTest`.

## 1. The finding: IC3 was starved of conservation laws

**Symptom.** Reachability-safety queries (`placeBound`, `unreachable`) on that net timed out at
120–600 s, while two structurally identical queries proved in <1 s. Long-standing oddity in the
consumer project: "SMT tests for short paths take 50 s".

**Cause.** `SmtVerifier` Phase 3 hands the encoder only the *null-space basis* from
`PInvariantComputer.computeChecked`, filtered to semi-positive rows and then by the H1 guard
(any row weighted on a reset / consume-all place is dropped — sound, see
`Strengthening.lean`). A null-space basis is one of many; Gaussian elimination returns
mixed-sign rows (discarded) and rows that fold a reset place into a chain whose other
combinations avoid it (dropped). On a net with ~15 reset arcs this left **3** invariants of the
~15 minimal laws. The two fast queries were exactly the ones covered by a surviving law; IC3
never rediscovered the others.

`computePSemiflows` (Farkas/Colom–Silva, already computed for the colour-slot bound) returns
the minimal semi-positive laws; after `validateExact` they are sound invariants with zero
weight on every H1 place.

**Change** (`SmtVerifier.semiflowInvariants(boolean)`, default off): union the validated
semiflows into the invariant list the encoders receive. Report line
`  Semiflows encoded as invariants: N` only when enabled, so byte-parity of reports is
unchanged by default. Test: `SemiflowInvariantsTest` (encoded only when enabled; a genuine
violation stays VIOLATED).

**Effect on the consumer net** (session net, three env places `bounded(2)`, 10 queries):
3.0.1 → 2 proven (<1 s), 8 `Unknown` at 120 s. With the option → 9 proven in 0.8–1.6 s each;
the tenth (`unreachable(TEXT_RESPONSE, TOOL_REQUEST)`) is not an invariant of that net.

**Rejected alternative** (tried, reverted): projecting the H1 places out *before* the null-space
elimination. Sound and cheap, but the basis still comes back mixed-sign — it found nothing new.

## 2. What a proper change needs (the ask for this session)

1. **Spec.** New requirement under `spec/` (VER family; "Invariant strengthening from
   P-semiflows"), ACs: semiflows are re-validated with the same exact gate as basis rows;
   encoded only when the option is on; report line; `Proven` never weakened (certificate check
   re-proves the strengthened invariant — verify `CertificateChecker` receives the same list).
2. **Lean.** `Strengthening.lean` already carries VER-005 (invariant strengthening soundness for
   the null-space rows: a valid `y·M = y·M0` law conjoined into the CHC body removes no reachable
   successor, under H1 `ZeroOnNonlinear`). The semiflow rows satisfy the same hypotheses
   (`y ≥ 0`, `y·C = 0`, `ZeroOnNonlinear` by `validateExact`) — state the theorem once over "any
   validated law" and cite it for both sources, or add a corollary. Add the fragment to
   `lean/proof-coverage.json` and regenerate `spec/coverage-matrix.md`.
3. **Ports.** Rust (`name_coloured_encoder.rs` sibling: the verifier's Phase 3), TypeScript,
   Python: same option, same report line, same test. `VerdictParityTest` / cross-language
   parity scripts must stay byte-equal with the option off.
4. **Default.** Consider on-by-default in the next major (4.x): it is pure strengthening. Off in
   3.x to keep report parity.
5. **CHANGELOG** entry; `scripts/release-java.sh 3.1.0`.

## 3. Two smaller findings on the same branch (separate commits / PRs)

**Route B memory (`NameStateClassGraph`).** `jmap -histo:live` at 1.8M classes (20 g heap):
4.2 KB per class — 1.75 KB `NameMarking` (TreeMap-of-TreeMaps), 650 B canonical-key String,
~580 B DBM rows + `readyEarliest`, ~300 B `MarkingState`, ~200 B edges. The branch hash-conses
the base `StateClass` (equality is marking + zone) and the name layer by canonical key
(`NameStateClass` got a precomputed-key constructor). Semantics-preserving: every consumer of
the layer is symmetric under renaming and mint freshness is a monotone counter. **Unmeasured
benefit** — the session net still exceeded 20 g at ~5M classes before it was measured; the
consumer moved to slices + IC3 instead. Expected ~3× per class. A further step is replacing the
TreeMaps with compact int arrays and dropping the `edges` list for BFS parent pointers.

**k = 0 refuses the coloured plan.** `NameColouredEncoder.buildPlan` returns `null` when the
semiflow bound is 0 (`sumConst >= 1`). For a mid-phase marking where no budget token exists no
coloured token can ever be produced, so the name-blind encoding is exact — yet the verifier
downgrades quiescence to `Unknown`. Accepting `k = 0` as an exact (vacuous colour layer) plan
would decide those queries. Consumer workaround: seed the budget place.

## 4. Things worth knowing that are *not* library bugs

- Route A's coloured encoding (13 slots × 30 coloured places) never converged on the session
  net (UNKNOWN after 50 min); Route B closes each of three slices in seconds (~48k classes) and
  exhausts the heap on the whole net — 5 parallel axes × a re-ask loop, no partial-order
  reduction. POR (stubborn sets) in `NameStateClassGraph` would be the scalability lever.
- `Z3 exception: canceled` after ~1 s when several `SmtVerifier`s run concurrently in one JVM
  (JUnit `@Execution(CONCURRENT)`): worth checking whether the Z3 timeout/interrupt is global.
- `budgetPlaces` is not validated (a typo silently yields `Unknown`); `carrierPlaces` throws.
- The EXTENDED relay/drain contract on actions is unverifiable by the library; the consumer
  verified it by hand. A `bindActions`-time lint (relay action must forward a name it consumed)
  would be the checkable version.
