import { describe, it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { deadlockFree } from '../../src/verification/smt-property.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace, andPlaces } from '../../src/core/out.js';
import { matchSpec, matchKey } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { delayed } from '../../src/core/timing.js';
import { NameStateClassGraph } from '../../src/verification/analysis/name-state-class-graph.js';
import { classify } from '../../src/verification/analysis/name-fragment.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import type { PrioritySemantics } from '../../src/verification/analysis/priority-semantics.js';
import { bindProducers } from '../fixtures/producing-actions.js';

/**
 * Verify-locally-first proof of the `'conflict'` PrioritySemantics (NU-052) on a
 * minimal fixture reproducing the Marvin guard-join vs. timed dead-letter-drain
 * conflict.
 *
 * Fixture: a fork (`MINT`) co-mints ONE fresh name into the two join inputs
 * `COL_A` and `COL_B`; an immediate, default-priority ν-`JOIN` matches them into
 * `OUT`; a delayed, lower-priority `DRAIN_A` consumes `COL_A` into `DEADLETTER`.
 * `DRAIN_A` and `JOIN` conflict on `COL_A`.
 *
 * - `'none'` (priority/timing-blind, default): the graph explores `DRAIN_A`
 *   firing while the join is enabled and matched, consuming `COL_A` and stranding
 *   `COL_B` — a spurious stall the eager, priority-ordered executor cannot
 *   exhibit (the join is immediate and higher-priority). VIOLATED.
 * - `'conflict'`: `DRAIN_A` is pruned while the higher-priority, no-later-ready
 *   join is enabled, so the join always fires. PROVEN via Route B.
 * - `'conflict'`, genuine orphan: when `COL_A` really has no matching `COL_B` the
 *   join is not enabled, so nothing prunes the drain — it must not over-prune.
 */
describe('NameStateClassGraph conflict-only priority (NU-052)', () => {
  const SEED = place('SEED');
  const COL_A = place<string>('COL_A');
  const COL_B = place<string>('COL_B');
  const OUT = place<string>('OUT');
  const DEADLETTER = place<string>('DEADLETTER');

  /**
   * @param coMintBoth mint one name into both join inputs (true) or only `COL_A` (orphan)
   * @param withDrain  include the delayed, low-priority `COL_A` dead-letter drain
   */
  function fixture(coMintBoth: boolean, withDrain: boolean): PetriNet {
    const mint = Transition.builder('MINT')
      .inputs(one(SEED))
      .outputs(coMintBoth ? andPlaces(COL_A, COL_B) : outPlace(COL_A))
      .build();
    const join = Transition.builder('JOIN') // immediate, priority 0
      .inputs(one(COL_A), one(COL_B))
      .match(matchSpec(matchKey(COL_A, (s: string) => nameId(s)), matchKey(COL_B, (s: string) => nameId(s))))
      .outputs(outPlace(OUT))
      .build();
    const transitions = [mint, join];
    if (withDrain) {
      transitions.push(
        Transition.builder('DRAIN_A') // delayed, lower priority, conflicts on COL_A
          .inputs(one(COL_A))
          .timing(delayed(5_000))
          .priority(-10)
          .outputs(outPlace(DEADLETTER))
          .build(),
      );
    }
    return PetriNet.builder('priorityFixture').transitions(...transitions).build();
  }

  const verifier = (net: PetriNet) =>
    SmtVerifier.forNet(bindProducers(net))
      .initialMarking(m => m.tokens(SEED, 1))
      .property(deadlockFree())
      .sinkPlaces(OUT, DEADLETTER)
      .fragmentMode('extended');

  it('priority-blind (none, default) reports the spurious stall', async () => {
    const r = await verifier(fixture(true, true)).verify(); // 'none' is the default
    expect(r.report).toContain('Route B');
    // The drain steals the matched COL_A and strands COL_B — a spurious stall.
    expect(r.verdict.type).toBe('violated');
  });

  it('conflict priority proves no stall', async () => {
    const r = await verifier(fixture(true, true)).prioritySemantics('conflict').verify();
    expect(r.report).toContain('Route B');
    // The immediate, higher-priority join pre-empts the delayed drain, so COL_A is
    // never stolen from a live join.
    expect(r.verdict.type).toBe('proven');
  });

  it('conflict priority still finds a genuine stall', async () => {
    // A real orphan (COL_A with no matching COL_B) and no drain: the join can never
    // fire and COL_A strands. CONFLICT must NOT hide this — the join is not
    // enabled, so nothing is pruned.
    const r = await verifier(fixture(false, false)).prioritySemantics('conflict').verify();
    expect(r.report).toContain('Route B');
    expect(r.verdict.type).toBe('violated');
  });

  it('conflict priority lets the drain clear a real orphan', async () => {
    // A real orphan WITH the drain present: CONFLICT does not prune the drain (the
    // join is not enabled), so the orphan is dead-lettered and the net is
    // deadlock-free.
    const r = await verifier(fixture(false, true)).prioritySemantics('conflict').verify();
    expect(r.verdict.type).toBe('proven');
    expect(r.report).not.toContain('declined');
  });
});

/**
 * NU-052 Part A: DBM residual-earliest prune + multiplicity guard, exercised
 * directly against {@link NameStateClassGraph} so the prune is observed as
 * reachability of `DEADLETTER`.
 */
describe('NameStateClassGraph residual-earliest prune (NU-052 Part A)', () => {
  const SEED = place('SEED');
  const COL_A = place<string>('COL_A');
  const COL_B = place<string>('COL_B');
  const OUT = place<string>('OUT');
  const DEADLETTER = place<string>('DEADLETTER');

  // MINT co-mints one fresh name into COL_A + COL_B; a DELAYED higher-priority
  // JOIN (delayed 100) matches them into OUT; a DELAYED lower-priority DRAIN_A
  // (delayed 200) dead-letters COL_A. The old `earliest === 0` guard could not
  // prune a non-immediate H; the residual-earliest predicate can.
  function delayedFixture(): PetriNet {
    const mint = Transition.builder('MINT')
      .inputs(one(SEED))
      .outputs(andPlaces(COL_A, COL_B))
      .build();
    const join = Transition.builder('JOIN') // delayed 100, default priority
      .inputs(one(COL_A), one(COL_B))
      .timing(delayed(100))
      .match(matchSpec(matchKey(COL_A, (s: string) => nameId(s)), matchKey(COL_B, (s: string) => nameId(s))))
      .outputs(outPlace(OUT))
      .build();
    const drain = Transition.builder('DRAIN_A') // delayed 200, lower priority
      .inputs(one(COL_A))
      .timing(delayed(200))
      .priority(-10)
      .outputs(outPlace(DEADLETTER))
      .build();
    return PetriNet.builder('delayedPriorityFixture').transitions(mint, join, drain).build();
  }

  function reachesDeadletter(net: PetriNet, initial: MarkingState, ps: PrioritySemantics): boolean {
    const fragment = classify(net, 'extended', new Set())!;
    const graph = NameStateClassGraph.build(net, initial, fragment, 10_000, undefined, undefined, ps);
    for (let i = 0; i < graph.classCount(); i++) {
      if (graph.markingOf(i).tokens(DEADLETTER) > 0) return true;
    }
    return false;
  }

  it('conflict prunes a DELAYED lower-priority drain (residual-earliest)', () => {
    const net = delayedFixture();
    const initial = MarkingState.builder().tokens(SEED, 1).build();
    // NONE explores the drain; CONFLICT prunes it because the delayed join becomes
    // ready first (0.1s < 0.2s) and takes COL_A — a case the old earliest-0 guard
    // could not prune.
    expect(reachesDeadletter(net, initial, 'none')).toBe(true);
    expect(reachesDeadletter(net, initial, 'conflict')).toBe(false);
  });

  it('conflict does NOT prune when the shared place holds enough tokens (multiplicity)', () => {
    // SEED=2 lets MINT co-mint two distinct names, so COL_A can hold 2 tokens. With
    // both demands (join + drain, 1 each) satisfiable at once, the drain does not
    // compete and must not be pruned — DEADLETTER stays reachable under CONFLICT.
    const net = delayedFixture();
    const initial = MarkingState.builder().tokens(SEED, 2).build();
    expect(reachesDeadletter(net, initial, 'conflict')).toBe(true);
  });

  it('does NOT prune when H only READS the shared place (NU-052 criterion 4)', () => {
    // A READ arc on the shared place is not a consumption conflict, so CONFLICT must
    // NOT prune the lower-priority consumer. H (priority 10) only READS SH; DRAIN
    // (priority -10) CONSUMES SH into DEADLETTER. Because sharesConsumedInput counts
    // only consumed inputs, H does not rob DRAIN of SH → DEADLETTER stays reachable
    // even under CONFLICT. (If H consumed SH this would be a genuine conflict and
    // CONFLICT would prune it.) A never-fired ν-JOIN (its coloured inputs start
    // empty) makes the net a ν-net so it classifies; the SH conflict is uncoloured
    // (coloured places may not carry read arcs — classify's soundness guard).
    const SH = place('SH');
    const TOK_H = place('TOK_H');
    const join = Transition.builder('JOIN')
      .inputs(one(COL_A), one(COL_B))
      .match(matchSpec(matchKey(COL_A, (s: string) => nameId(s)), matchKey(COL_B, (s: string) => nameId(s))))
      .outputs(outPlace(OUT))
      .build();
    const h = Transition.builder('H') // higher priority, only READS SH
      .inputs(one(TOK_H))
      .read(SH)
      .priority(10)
      .outputs(outPlace(OUT))
      .build();
    const drain = Transition.builder('DRAIN') // lower priority, CONSUMES SH
      .inputs(one(SH))
      .priority(-10)
      .outputs(outPlace(DEADLETTER))
      .build();
    const net = PetriNet.builder('readArcFixture').transitions(join, h, drain).build();
    const initial = MarkingState.builder().tokens(TOK_H, 1).tokens(SH, 1).build();

    expect(reachesDeadletter(net, initial, 'none')).toBe(true);
    expect(reachesDeadletter(net, initial, 'conflict')).toBe(true);
  });
});
