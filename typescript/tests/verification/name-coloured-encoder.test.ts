import { describe, it, expect } from 'vitest';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace, andPlaces } from '../../src/core/out.js';
import { matchSpec, matchKey } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import { buildColouredPlan } from '../../src/verification/z3/name-coloured-encoder.js';

// Z3-free conformance for the name-coloured fragment gate (buildColouredPlan).
// Pins nu-1: a budget-inflating ν-net (a join refunding more budget than a mint
// consumes) must fall back to the sound over-approximation rather than take the
// exact, caveat-dropped name-coloured path.
describe('name-coloured fragment gate (nu-1 budget conservation)', () => {
  // A budget-bounded mint→join net (same-mint scatter-gather): one mint consumes
  // 1 budget and stamps the fresh colour into both correlated inputs; the join
  // refunds 1 budget (conserving) or 2 (inflating, into a 2nd budget place).
  function mintJoinNet(inflating: boolean) {
    const budget1 = place('budget1');
    const budget2 = place('budget2');
    const a = place<string>('branchA');
    const b = place<string>('branchB');

    const mint = Transition.builder('mint')
      .inputs(one(budget1))
      .outputs(andPlaces(a, b))
      .build();
    const joinOut = inflating ? andPlaces(budget1, budget2) : outPlace(budget1);
    const join = Transition.builder('join')
      .inputs(one(a), one(b))
      .match(matchSpec(
        matchKey(a, (s: string) => nameId(s)),
        matchKey(b, (s: string) => nameId(s)),
      ))
      .outputs(joinOut)
      .build();
    const net = PetriNet.builder('mintJoin').transitions(mint, join).build();
    return { net, budget1 };
  }

  function planFor(inflating: boolean) {
    const { net, budget1 } = mintJoinNet(inflating);
    const flat = flatten(net);
    const initial = MarkingState.builder().tokens(budget1, 1).build();
    return buildColouredPlan(net, flat, initial, new Set(['budget1', 'budget2']));
  }

  it('takes the exact path when the join conserves budget', () => {
    // Refund (1) == mint cost (1): live names ≤ k.
    expect(planFor(false)).not.toBeNull();
  });

  it('falls back to the over-approximation when the join inflates budget', () => {
    // nu-1: a join refunding 2 budget for a 1-budget mint inflates the pool above
    // k — the k-colour encoder would UNDER-approximate and report a false Proven.
    expect(planFor(true)).toBeNull();
  });
});
