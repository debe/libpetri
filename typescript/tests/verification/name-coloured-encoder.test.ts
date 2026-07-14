import { describe, it, expect } from 'vitest';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace, andPlaces, xorPlaces } from '../../src/core/out.js';
import { matchSpec, matchKey } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import { computePSemiflows } from '../../src/verification/invariant/p-invariant-computer.js';
import { IncidenceMatrix } from '../../src/verification/encoding/incidence-matrix.js';
import { buildColouredPlan } from '../../src/verification/z3/name-coloured-encoder.js';
import type { FragmentMode } from '../../src/verification/analysis/name-fragment.js';

// Z3-free conformance for the name-coloured fragment gate (buildColouredPlan).
// The colour-slot bound `k` comes from a non-negative P-semiflow that weights every
// coloured place: a net whose coloured set has no covering semiflow (an unbounded
// colour leak) falls back to the sound over-approximation; a colour-bounded net is
// admitted for the exact name-coloured path.
describe('name-coloured fragment gate (colour-slot bound)', () => {
  // A budget-bounded mint→join net (same-mint scatter-gather): one mint consumes
  // 1 budget and stamps the fresh colour into both correlated inputs; the join
  // refunds 1 budget (conserving) or refunds an EXTRA token to a non-minting place
  // (budget2) — either way the MINTING budget (budget1) stays conserved, so at most
  // one colour is ever live and the P-semiflow bound admits it.
  function mintJoinNet(extraRefund: boolean) {
    const budget1 = place('budget1');
    const budget2 = place('budget2');
    const a = place<string>('branchA');
    const b = place<string>('branchB');

    const mint = Transition.builder('mint')
      .inputs(one(budget1))
      .outputs(andPlaces(a, b))
      .build();
    const joinOut = extraRefund ? andPlaces(budget1, budget2) : outPlace(budget1);
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

  function planFor(extraRefund: boolean) {
    const { net, budget1 } = mintJoinNet(extraRefund);
    const flat = flatten(net);
    const initial = MarkingState.builder().tokens(budget1, 1).build();
    const semiflows = computePSemiflows(IncidenceMatrix.from(flat), flat, initial);
    return buildColouredPlan(net, flat, initial, new Set(['budget1', 'budget2']), 'base', new Set(), semiflows);
  }

  it('takes the exact path when the join conserves budget', () => {
    // Refund (1) == mint cost (1): live names ≤ k.
    expect(planFor(false)).not.toBeNull();
  });

  it('admits a join that refunds an extra token to a non-minting place', () => {
    // [NU-053] The extra refund lands in budget2 (a non-minting place), so the minting
    // budget stays conserved and at most one colour is live — the net is colour-bounded
    // and the P-semiflow bound admits it. (The old budget-Φ heuristic wrongly rejected
    // any refund exceeding the mint cost; genuine colour leaks — where a co-minted place
    // accumulates distinct colours — are covered by the leaky-carrier fan-out test below,
    // which still falls back.)
    expect(planFor(true)).not.toBeNull();
  });
});

// === NU-053: EXTENDED coloured-consumer fragment + XOR expansion ===
describe('name-coloured fragment gate (NU-053 EXTENDED + XOR)', () => {
  // Shared driver: flatten, seed budget1=1, and run the gate under `mode`/`carriers`.
  function planFor(net: PetriNet, mode: FragmentMode, carriers: string[]) {
    const flat = flatten(net);
    const budget1 = place('budget1');
    const initial = MarkingState.builder().tokens(budget1, 1).build();
    const semiflows = computePSemiflows(IncidenceMatrix.from(flat), flat, initial);
    return buildColouredPlan(
      net, flat, initial, new Set(['budget1', 'budget2']), mode, new Set(carriers), semiflows,
    );
  }

  // mint→join plus an EXTENDED coloured drain: a non-match transition that consumes
  // one correlated input `a` (count 1) into a plain sink. Rejected under BASE,
  // admitted under EXTENDED.
  function mintJoinDrainNet() {
    const budget1 = place('budget1');
    const a = place<string>('branchA');
    const b = place<string>('branchB');
    const sink = place<string>('sink');

    const mint = Transition.builder('mint').inputs(one(budget1)).outputs(andPlaces(a, b)).build();
    const join = Transition.builder('join')
      .inputs(one(a), one(b))
      .match(matchSpec(matchKey(a, (s: string) => nameId(s)), matchKey(b, (s: string) => nameId(s))))
      .outputs(outPlace(budget1))
      .build();
    const drain = Transition.builder('drain').inputs(one(a)).outputs(outPlace(sink)).build();
    return PetriNet.builder('mintJoinDrain').transitions(mint, join, drain).build();
  }

  // mint→join with an EXTENDED carrier relay: the fork co-mints into `carrier` and
  // join input `b`; the relay threads `carrier`'s name into the other join input
  // `a`. `carrier` is coloured only when declared as a carrier under EXTENDED. When
  // `relayRefunds`, the relay also refunds budget — which must be rejected, since a
  // relay keeps the colour live.
  function mintRelayJoinNet(relayRefunds: boolean) {
    const budget1 = place('budget1');
    const carrier = place<string>('carrier');
    const a = place<string>('branchA');
    const b = place<string>('branchB');

    const mint = Transition.builder('mint').inputs(one(budget1)).outputs(andPlaces(carrier, b)).build();
    const relayOut = relayRefunds ? andPlaces(a, budget1) : outPlace(a);
    const relay = Transition.builder('relay').inputs(one(carrier)).outputs(relayOut).build();
    const join = Transition.builder('join')
      .inputs(one(a), one(b))
      .match(matchSpec(matchKey(a, (s: string) => nameId(s)), matchKey(b, (s: string) => nameId(s))))
      .outputs(outPlace(budget1))
      .build();
    return PetriNet.builder('mintRelayJoin').transitions(mint, relay, join).build();
  }

  // mint→join plus a plain XOR transition (uncoloured), which expands to two flat
  // rows — exercising Part 3 (no 1:1 net↔flat assumption).
  function mintJoinXorNet() {
    const budget1 = place('budget1');
    const a = place<string>('branchA');
    const b = place<string>('branchB');
    const s = place('s');
    const x = place('x');
    const y = place('y');

    const mint = Transition.builder('mint').inputs(one(budget1)).outputs(andPlaces(a, b)).build();
    const join = Transition.builder('join')
      .inputs(one(a), one(b))
      .match(matchSpec(matchKey(a, (v: string) => nameId(v)), matchKey(b, (v: string) => nameId(v))))
      .outputs(outPlace(budget1))
      .build();
    const branch = Transition.builder('branch').inputs(one(s)).outputs(xorPlaces(x, y)).build();
    return PetriNet.builder('mintJoinXor').transitions(mint, join, branch).build();
  }

  // A leaky fork ([NU-053] S2): the mint co-mints its colour into the join inputs
  // `branchA`, `branchB` AND a declared carrier `c`, but the join only re-collects
  // `branchA`, `branchB` and nothing ever consumes `c`. The colour outlives the budget
  // the join refunds, so the real net can hold more than k live colours while the
  // k-colour encoding gets stuck at the freshness guard.
  function mintLeakyCarrierNet() {
    const budget1 = place('budget1');
    const a = place<string>('branchA');
    const b = place<string>('branchB');
    const c = place<string>('c');

    const mint = Transition.builder('mint').inputs(one(budget1)).outputs(andPlaces(a, b, c)).build();
    const join = Transition.builder('join')
      .inputs(one(a), one(b))
      .match(matchSpec(matchKey(a, (s: string) => nameId(s)), matchKey(b, (s: string) => nameId(s))))
      .outputs(outPlace(budget1))
      .build();
    return PetriNet.builder('mintLeakyCarrier').transitions(mint, join).build();
  }

  it('rejects the EXTENDED drain under BASE, admits it under EXTENDED', () => {
    // A non-match consumer of a coloured place is out-of-fragment under BASE and
    // admitted as a drain under EXTENDED.
    const net = mintJoinDrainNet();
    expect(planFor(net, 'base', [])).toBeNull();
    expect(planFor(net, 'extended', [])).not.toBeNull();
  });

  it('admits the carrier relay only under EXTENDED', () => {
    // The carrier place is coloured only when declared under EXTENDED; then the
    // relay threading its name to the join input is an admitted Consume.
    const net = mintRelayJoinNet(false);
    expect(planFor(net, 'base', [])).toBeNull();
    expect(planFor(net, 'extended', ['carrier'])).not.toBeNull();
  });

  it('rejects a relay that also refunds budget', () => {
    // A relay keeps the colour live; if it also refunded budget the freed token
    // could mint a (k+1)-th live colour. The gate must reject it.
    const net = mintRelayJoinNet(true);
    expect(planFor(net, 'extended', ['carrier'])).toBeNull();
  });

  it('rejects a fork whose fan-out is not re-collected by one join', () => {
    // [NU-053] S2: the mint fans its colour into branchA, branchB AND carrier c, but the
    // refunding join only re-collects branchA, branchB — c is never consumed, so the
    // colour outlives its refunded budget and the real net can hold more than k live
    // colours. The gate must reject this (null → sound over-approximation) rather than
    // certify an exact plan the quiescence gate would trust for a false Proven. Contrast
    // the admitted carrier-relay case, where the fork's carrier branch is relayed back
    // into a join input (atomic re-collection).
    expect(planFor(mintLeakyCarrierNet(), 'extended', ['c'])).toBeNull();
  });

  it('no longer blocks the coloured plan on an XOR transition', () => {
    // A plain XOR transition expands to two flat rows; Part 3 drops the old 1:1
    // net↔flat rejection so the mint→join fragment is still recognised.
    const net = mintJoinXorNet();
    expect(planFor(net, 'base', [])).not.toBeNull();
  });
});
