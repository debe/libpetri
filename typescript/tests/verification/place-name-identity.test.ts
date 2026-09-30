import { describe, it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import type { SmtVerificationResult } from '../../src/verification/smt-verification-result.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { StateClassGraph } from '../../src/verification/analysis/state-class-graph.js';
import { TimePetriNetAnalyzer } from '../../src/verification/analysis/time-petri-net-analyzer.js';
import { alwaysAvailable } from '../../src/verification/analysis/environment-analysis-mode.js';
import {
  deadlockFree, mutualExclusion, placeBound, quiescentCount, unreachable,
} from '../../src/verification/smt-property.js';
import { produces } from '../fixtures/producing-actions.js';
import { describeZ3 } from '../fixtures/z3.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { Interface } from '../../src/core/interface.js';
import { place, environmentPlace, type Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { and, outPlace } from '../../src/core/out.js';
import { matchKey, matchSpec } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { tokenOf } from '../../src/core/token.js';

/**
 * TypeScript places are identified by name (CLAUDE.md, the [MOD-024] note): `place('E')` twice
 * gives two objects that are one place. Verification reads them as one, as Rust (name-only
 * equality) and Java (record equality on name and token type) do. Each test states a net or a
 * declaration twice, once with one object per place and once with a second object of the same
 * name at one site, and expects the same answer.
 */

const key = (s: string) => nameId(s);

/** mint: budget -> A + B, J: A, B -> done matched by name, and t: E -> out beside them. */
const nuNet = (arcE: Place<string>) => PetriNet.builder('env_identity').transitions(
  Transition.builder('mint').inputs(one(place('budget'))).outputs(and(outPlace(place('A')), outPlace(place('B'))))
    .action(produces()).build(),
  Transition.builder('J').inputs(one(place('A')), one(place('B')))
    .match(matchSpec(matchKey(place('A'), key), matchKey(place('B'), key)))
    .outputs(outPlace(place('done'))).action(produces()).build(),
  Transition.builder('t').inputs(one(arcE)).outputs(outPlace(place('out'))).action(produces()).build(),
).build();

/** t: E -> out, a plain net. */
const plainNet = (arcE: Place<string>) => PetriNet.builder('env_plain').transitions(
  Transition.builder('t').inputs(one(arcE)).outputs(outPlace(place('out'))).action(produces()).build(),
).build();

/** Every result projects to what the first one projects to. */
const same = <T>(results: readonly T[], project: (r: T) => unknown): void => {
  expect(results.map(project)).toEqual(results.map(() => project(results[0]!)));
};

describe('environment places are matched by name (VER-006)', () => {
  const envE = environmentPlace<string>('E');

  it('Route B injects into E whichever E object the arc names (NU-050)', async () => {
    const verify = (arcE: Place<string>) => SmtVerifier.forNet(nuNet(arcE))
      .initialMarking(m => m.tokens(place('budget'), 1))
      .environmentPlaces(envE)
      .mintTransitions('mint')
      .property(unreachable(new Set([place('out')])))
      .verify();
    const shared = await verify(envE.place);
    const separate = await verify(place<string>('E'));
    expect(shared.route, shared.report).toBe('nu-scg');
    expect(shared.verdict.type, shared.report).toBe('violated');
    expect(separate.route, separate.report).toBe('nu-scg');
    expect(separate.verdict.type, separate.report).toBe('violated');
  });

  it('StateClassGraph.build supplies E whichever E object the arc names', () => {
    const reached = (arcE: Place<string>) => StateClassGraph.build(
      plainNet(arcE), MarkingState.empty(), 100, new Set([envE]), alwaysAvailable(),
    ).reachableMarkings();
    expect(reached(envE.place)).toContain('{out:1}');
    expect(reached(place<string>('E'))).toContain('{out:1}');
  });

  it('TimePetriNetAnalyzer reaches the goal whichever E object the arc names', () => {
    const goalReached = (arcE: Place<string>) => TimePetriNetAnalyzer.forNet(plainNet(arcE))
      .goalPlaces(place('out'))
      .environmentPlaces(envE)
      .environmentMode(alwaysAvailable())
      .maxClasses(20)
      .build()
      .analyze().goalClasses.size > 0;
    expect(goalReached(envE.place)).toBe(true);
    expect(goalReached(place<string>('E'))).toBe(true);
  });
});

describe('SubnetDef.verify feeds its input ports (MOD-051)', () => {
  // The harness registers `environmentPlace('harness_in_req')`, a different object from the
  // place its compose binds on the arcs, so this is the library's own use of the idiom.
  it('a ν subnet fed through an input port reaches its output on Route B', async () => {
    const req = place<string>('req');
    const done = place<string>('done');
    const def = SubnetDef.builder('Correlate')
      .transitions(
        Transition.builder('mint').inputs(one(req)).outputs(and(outPlace(place('A')), outPlace(place('B'))))
          .action(produces()).build(),
        Transition.builder('J').inputs(one(place('A')), one(place('B')))
          .match(matchSpec(matchKey(place('A'), key), matchKey(place('B'), key)))
          .outputs(outPlace(done)).action(produces()).build(),
      )
      .inputPort('req', req)
      .outputPort('done', done)
      .build();
    const result = await def.verify(
      {
        params: undefined as never,
        portInputGenerators: { req: () => tokenOf('x') },
        properties: [unreachable(new Set([place('harness_out_done')]))],
      },
      { configure: v => v.mintTransitions('sut/mint') },
    );
    const r = [...result.perProperty.values()][0]!;
    expect(r.route, r.report).toBe('nu-scg');
    expect(r.verdict.type, r.report).toBe('violated');
  });
});

describe('subnet ports are matched by name (MOD-006, MOD-014)', () => {
  const body = () => Transition.builder('forward').inputs(one(place('in'))).outputs(outPlace(place('out')))
    .action(produces()).build();

  it('SubnetDef.builder accepts a port place that is another object of a body place', () => {
    const def = SubnetDef.builder('Forward').transition(body())
      .inputPort('in', place('in'))
      .outputPort('out', place('out'))
      .build();
    expect([...def.iface.ports.keys()]).toEqual(['in', 'out']);
  });

  it('SubnetDef.fromNet accepts a port place that is another object of a net place', () => {
    const net = PetriNet.builder('Forward').transition(body()).build();
    const iface = Interface.builder().inputPort('in', place('in')).outputPort('out', place('out')).build();
    expect(SubnetDef.fromNet(net, iface).name).toBe('Forward');
  });

  it('a port place the body does not have is still rejected', () => {
    expect(() => SubnetDef.builder('Forward').transition(body()).inputPort('in', place('elsewhere')).build())
      .toThrow("port 'in' references place 'elsewhere' which is not in the body");
  });
});

/**
 * The sites below already key by name. They are pinned so that a change back to object identity
 * fails a test: each verdict is the same with a shared object and a separate one.
 */
describeZ3('declarations and properties are read by name', () => {
  // start -> mid -> end, all immediate; `end` is where a run rests.
  const chain = (endAtArc: Place<string>) => PetriNet.builder('chain').transitions(
    Transition.builder('a').inputs(one(place('start'))).outputs(outPlace(place('mid'))).action(produces()).build(),
    Transition.builder('b').inputs(one(place('mid'))).outputs(outPlace(endAtArc)).action(produces()).build(),
  ).build();
  const end = place<string>('end');
  const both = [end, place<string>('end')];
  const run = (net: PetriNet, configure: (v: SmtVerifier) => SmtVerifier): Promise<SmtVerificationResult> =>
    configure(SmtVerifier.forNet(net).initialMarking(m => m.tokens(place('start'), 1))).verify();

  it('sink places', async () => {
    const results = await Promise.all(both.map(arc =>
      run(chain(arc), v => v.property(deadlockFree()).sinkPlaces(end))));
    expect(results[0]!.verdict.type, results[0]!.report).toBe('proven');
    same(results, r => r.verdict.type);
  });

  it('conditional sinks', async () => {
    const results = await Promise.all(both.map(arc =>
      run(chain(arc), v => v.property(deadlockFree()).sinkPlacesWhen(end))));
    expect(results[0]!.verdict.type, results[0]!.report).toBe('proven');
    same(results, r => r.verdict.type);
  });

  it('property places: unreachable, placeBound, mutualExclusion, quiescentCount', async () => {
    const properties = [
      unreachable(new Set([end])),
      placeBound(end, 0),
      mutualExclusion(end, place('start')),
      quiescentCount([end], 0, 0),
    ];
    for (const property of properties) {
      const results = await Promise.all(both.map(arc =>
        run(chain(arc), v => v.property(property).sinkPlaces(end))));
      same(results, r => r.verdict.type);
    }
  });

  it('a net that holds two objects of one place reports it as one place', async () => {
    const net = PetriNet.builder('chain').place(place('end')).transitions(
      Transition.builder('a').inputs(one(place('start'))).outputs(outPlace(place('mid'))).action(produces()).build(),
      Transition.builder('b').inputs(one(place('mid'))).outputs(outPlace(place('end'))).action(produces()).build(),
    ).build();
    const r = await run(net, v => v.property(deadlockFree()).sinkPlaces(end));
    expect(r.route, r.report).toBe('enumeration');
    expect(r.statistics.places).toBe(3);
  });

  it('a quiescent count names two objects of one place and counts it once', async () => {
    const r = await run(chain(end), v => v.property(quiescentCount(both, 1, 1)).sinkPlaces(end));
    expect(r.verdict.type, r.report).toBe('proven');
  });

  it('terminal places', async () => {
    const net = (terminal: Place<string>) => PetriNet.builder('terminal').transitions(
      Transition.builder('a').inputs(one(place('start'))).outputs(and(outPlace(end), outPlace(place('left'))))
        .action(produces()).build(),
    ).terminal(terminal).build();
    const results = await Promise.all(both.map(t => run(net(t), v => v.property(deadlockFree()))));
    expect(results[0]!.verdict.type, results[0]!.report).toBe('proven');
    same(results, r => r.verdict.type);
  });

  it('match keys naming another object of the input place', async () => {
    const joinNet = (keyA: Place<string>) => PetriNet.builder('join').transitions(
      Transition.builder('mint').inputs(one(place('budget'))).outputs(and(outPlace(place('A')), outPlace(place('B'))))
        .action(produces()).build(),
      Transition.builder('J').inputs(one(place('A')), one(place('B')))
        .match(matchSpec(matchKey(keyA, key), matchKey(place('B'), key)))
        .outputs(outPlace(place('done'))).action(produces()).build(),
    ).build();
    const results = await Promise.all([place<string>('A'), place<string>('A')].map(k =>
      SmtVerifier.forNet(joinNet(k))
        .initialMarking(m => m.tokens(place('budget'), 1))
        .mintTransitions('mint')
        .property(unreachable(new Set([place('done')])))
        .verify()));
    expect(results[0]!.verdict.type, results[0]!.report).toBe('violated');
    same(results, r => [r.route, r.verdict.type]);
  });
});
