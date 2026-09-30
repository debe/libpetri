import { describe, it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { mutualExclusion, unreachable } from '../../src/verification/smt-property.js';
import { verifyViaNameScg } from '../../src/verification/nu-scg-verifier.js';
import { NameStateClassGraph } from '../../src/verification/analysis/name-state-class-graph.js';
import { classify } from '../../src/verification/analysis/name-fragment.js';
import { ignore } from '../../src/verification/analysis/environment-analysis-mode.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { andPlaces, outPlace } from '../../src/core/out.js';
import { matchKey, matchSpec } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { deadline, delayed, exact, window, type Timing } from '../../src/core/timing.js';
import { bindProducers } from '../fixtures/producing-actions.js';
import { allMints } from '../fixtures/all-mints.js';

/**
 * Route B clocks follow a ν-join's name-enabledness ([NU-020], [TIME-012]). The executor enables
 * a join only while one name is present in every correlated input, and a removal that breaks the
 * binding restarts its clock. Mirrors `rust/libpetri-verification/src/nu_scg_verifier.rs`
 * (`a_name_disabled_join_has_no_clock`, `a_join_clock_starts_when_its_binding_appears`) and
 * `name_state_class_graph.rs` (`a_broken_binding_in_the_intermediate_marking_restarts_the_join_clock`).
 */

const key = (v: string) => nameId(v);
const p = (n: string) => place<string>(n);

/**
 * `forkA` and `forkB` mint one name each (`deadline(1)`), `forkC` co-mints one name into both at
 * `exact(5)` when `withCoMint`, `join` matches the two on the name, `watchdog: W -> BAD`.
 */
function clockedJoinNet(joinTiming: Timing, watchdogTiming: Timing, withCoMint: boolean): PetriNet {
  const mint = (name: string, from: string, to: string[], timing: Timing) =>
    Transition.builder(name).inputs(one(p(from))).outputs(andPlaces(...to.map(p))).timing(timing).build();
  const ts = [
    mint('forkA', 'sourceA', ['branchA'], deadline(1)),
    mint('forkB', 'sourceB', ['branchB'], deadline(1)),
    Transition.builder('join')
      .inputs(one(p('branchA')), one(p('branchB')))
      .match(matchSpec(matchKey(p('branchA'), key), matchKey(p('branchB'), key)))
      .outputs(outPlace(p('merged')))
      .timing(joinTiming)
      .build(),
    Transition.builder('watchdog').inputs(one(p('W'))).outputs(outPlace(p('BAD'))).timing(watchdogTiming).build(),
  ];
  if (withCoMint) ts.push(mint('forkC', 'sourceC', ['branchA', 'branchB'], exact(5)));
  return bindProducers(PetriNet.builder('clocked_join').transitions(...ts).build());
}

function strict(net: PetriNet, initial: MarkingState, property: Parameters<typeof verifyViaNameScg>[2]) {
  return verifyViaNameScg(
    net, initial, property, new Set(), new Set(), ignore(), 10_000, 'base', new Set(), allMints(net), 'none')!;
}

describe('Route B clocks follow name-enabledness (NU-020, TIME-012)', () => {
  it('a name-disabled join has no clock', async () => {
    const net = clockedJoinNet(window(0, 5), delayed(10), false);
    const initial = MarkingState.builder().tokens(p('sourceA'), 1).tokens(p('sourceB'), 1).tokens(p('W'), 1).build();
    const out = strict(net, initial, unreachable(new Set([p('BAD')])));
    expect(out.verdict.type).toBe('violated');
    expect(out.transitions).not.toContain('join');
    for (const noReaping of [true, false]) {
      const result = await SmtVerifier.forNet(net).mintTransitions(...allMints(net))
        .initialMarking(m => m.tokens(p('sourceA'), 1).tokens(p('sourceB'), 1).tokens(p('W'), 1))
        .property(unreachable(new Set([p('BAD')])))
        .assumeNoReaping(noReaping)
        .timeout(30_000)
        .verify();
      expect(result.route, result.report).toBe('nu-scg');
      expect(result.verdict.type, result.report).toBe('violated');
    }
  });

  it("a join's clock starts when its binding appears", () => {
    const net = clockedJoinNet(delayed(10), exact(12), true);
    const initial = MarkingState.builder()
      .tokens(p('sourceA'), 1).tokens(p('sourceB'), 1).tokens(p('sourceC'), 1).tokens(p('W'), 1).build();
    const out = strict(net, initial, mutualExclusion(p('merged'), p('W')));
    expect(out.verdict.type).toBe('proven');
  });

  it('a broken binding in the intermediate marking restarts the join clock', () => {
    const m0 = Transition.builder('M0').inputs(one(p('s0'))).outputs(outPlace(p('A'))).timing(deadline(1)).build();
    const m1 = Transition.builder('M1').inputs(one(p('s1'))).outputs(andPlaces(p('A'), p('B')))
      .timing(deadline(1)).build();
    const j = Transition.builder('J')
      .inputs(one(p('A')), one(p('B')))
      .match(matchSpec(matchKey(p('A'), key), matchKey(p('B'), key)))
      .outputs(outPlace(p('OUT')))
      .timing(delayed(10))
      .build();
    const r = Transition.builder('R').inputs(one(p('A')), one(p('go'))).outputs(outPlace(p('A')))
      .timing(delayed(3)).build();
    const net = bindProducers(PetriNet.builder('broken_binding').transitions(m0, m1, j, r).build());
    const fragment = classify(net, 'extended', new Set(), allMints(net));
    expect(fragment).not.toBeNull();
    const initial = MarkingState.builder().tokens(p('s0'), 1).tokens(p('s1'), 1).tokens(p('go'), 1).build();
    const graph = NameStateClassGraph.build(net, initial, fragment!, 10_000);
    expect(graph.isComplete()).toBe(true);
    const ready = new Set<number>();
    for (const e of graph.edges) {
      if (e.transitionName !== 'R') continue;
      const base = graph.classes[e.to]!.base;
      const k = base.enabledTransitions.findIndex(t => t.name === 'J');
      if (k >= 0) ready.add(Math.round(base.readyEarliest[k]! * 1000));
    }
    expect([...ready]).toContain(10);
    expect([...ready].some(ms => ms <= 8)).toBe(true);
  });
});
