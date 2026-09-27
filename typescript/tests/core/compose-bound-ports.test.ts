import { describe, expect, it } from 'vitest';
import { PetriNet } from '../../src/core/petri-net.js';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { FusionSet } from '../../src/core/fusion-set.js';
import { Transition } from '../../src/core/transition.js';
import { one } from '../../src/core/in.js';
import { outPlace, xorPlaces } from '../../src/core/out.js';
import { instancePrefixOf } from '../../src/export/index.js';
import { producer } from '../fixtures/subnet-fixtures.js';

/**
 * Instance composition and the port places it replaces:
 *
 * - [MOD-020] binding two ports of one instance to one host place, where a transition
 *   consumes from both, is rejected at compose with a message naming the binding;
 * - [MOD-027] an arc naming a port place that composition replaced by a host place is
 *   rejected at build, whichever order `compose` and the arc were added in;
 * - [MOD-040] `PetriNet.subnetOf` is the AUTO cluster rule's public accessor.
 */

/** A join subnet: `join` consumes one token from each of ports `a` and `b`. */
function joinDef(): SubnetDef<void> {
  const a = place<string>('a');
  const b = place<string>('b');
  const done = place<string>('done');
  return SubnetDef.builder('Join')
    .transition(Transition.builder('join').inputs(one(a), one(b)).outputs(outPlace(done)).build())
    .inputPort('a', a)
    .inputPort('b', b)
    .build();
}

/** The lab's shape: an `answer` subnet whose `in` port feeds `call`. */
function answerDef(): SubnetDef<void> {
  const input = place<string>('IN');
  const out = place<string>('OUT');
  return SubnetDef.builder('Answer')
    .transition(Transition.builder('call').inputs(one(input)).outputs(outPlace(out)).build())
    .inputPort('in', input)
    .outputPort('out', out)
    .build();
}

describe('port-binding collision (MOD-020)', () => {
  it('two ports bound to one host place feeding one transition are rejected, naming the binding', () => {
    const x = place<string>('X');
    const s = joinDef().instantiate('s');
    expect(() => PetriNet.builder('host').compose(s, { a: x as Place<unknown>, b: x as Place<unknown> }))
      .toThrowError(
        "ports 'a' and 'b' of instance 's' are both bound to host place 'X'; transition 's/join' " +
        "would consume from 'X' through two input arcs. Bind them to distinct places or use one port.",
      );
  });

  it('the typed bindings overload is rejected the same way', () => {
    const x = place<string>('X');
    const s = joinDef().instantiate('s');
    expect(() => PetriNet.builder('host').compose(s, (b) => {
      b.bindPort('a', x);
      b.bindPort('b', x);
    })).toThrowError(/ports 'a' and 'b' of instance 's' are both bound to host place 'X'/);
  });

  it('distinct host places compose', () => {
    const s = joinDef().instantiate('s');
    const net = PetriNet.builder('host')
      .compose(s, { a: place<string>('X') as Place<unknown>, b: place<string>('Y') as Place<unknown> })
      .build();
    expect([...net.transitions].map(t => t.name)).toEqual(['s/join']);
  });
});

describe('references to bound ports (MOD-027)', () => {
  const message =
    "place 'answer/IN' is port 'in' of instance 'answer', bound to host place 'A_IN' at compose; " +
    "reference 'A_IN' instead";

  it('a reset arc on the bound port place, added after compose, is rejected at build', () => {
    const answer = answerDef().instantiate('answer');
    const aIn = place<string>('A_IN');
    const kill = Transition.builder('hub_kill')
      .inputs(one(place<string>('KILL')))
      .reset(answer.port('in'))
      .build();
    const builder = PetriNet.builder('lab')
      .compose(answer, { in: aIn as Place<unknown> })
      .transition(kill);
    expect(() => builder.build()).toThrowError(message);
  });

  it('the same arc added before compose is rejected the same way', () => {
    const answer = answerDef().instantiate('answer');
    const kill = Transition.builder('hub_kill')
      .inputs(one(place<string>('KILL')))
      .reset(answer.port('in'))
      .build();
    const builder = PetriNet.builder('lab')
      .transition(kill)
      .compose(answer, { in: place<string>('A_IN') as Place<unknown> });
    expect(() => builder.build()).toThrowError(message);
  });

  it.each([
    ['an input', (p: Place<string>) => Transition.builder('t').inputs(one(p))],
    ['a read', (p: Place<string>) => Transition.builder('t').read(p)],
    ['an inhibitor', (p: Place<string>) => Transition.builder('t').inhibitor(p)],
    ['an output (inside an XOR)', (p: Place<string>) =>
      Transition.builder('t').outputs(xorPlaces(p, place<string>('other')))],
  ])('%s arc on the bound port place: rejected', (_kind, arc) => {
    const answer = answerDef().instantiate('answer');
    const builder = PetriNet.builder('lab')
      .compose(answer, { in: place<string>('A_IN') as Place<unknown> })
      .transition(arc(answer.port<string>('in')).build());
    expect(() => builder.build()).toThrowError(message);
  });

  it('referencing the host place instead builds', () => {
    const answer = answerDef().instantiate('answer');
    const aIn = place<string>('A_IN');
    const net = PetriNet.builder('lab')
      .compose(answer, { in: aIn as Place<unknown> })
      .transition(Transition.builder('hub_kill').inputs(one(place<string>('KILL'))).reset(aIn).build())
      .build();
    expect([...net.places].some(p => p.name === 'answer/IN')).toBe(false);
  });

  it('an unbound port place stays referencable', () => {
    const answer = answerDef().instantiate('answer');
    const net = PetriNet.builder('lab')
      .compose(answer, { out: place<string>('A_OUT') as Place<unknown> })
      .transition(Transition.builder('feed').inputs(one(place<string>('SRC'))).outputs(outPlace(answer.port<string>('in'))).build())
      .build();
    expect([...net.places].some(p => p.name === 'answer/IN')).toBe(true);
  });

  it('is checked after fusion: a retired port fused away into the host place builds', () => {
    const answer = answerDef().instantiate('answer');
    const aIn = place<string>('A_IN');
    const net = PetriNet.builder('lab')
      .compose(answer, { in: aIn as Place<unknown> })
      .transition(Transition.builder('hub_kill').inputs(one(place<string>('KILL'))).reset(answer.port('in')).build())
      .fuse(FusionSet.of('f', aIn, answer.port('in')))
      .build();
    const kill = [...net.transitions].find(t => t.name === 'hub_kill')!;
    expect(kill.resets.map(r => r.place.name)).toEqual(['A_IN']);
  });

  it('is checked after fusion: an arc fused onto a retired port as canonical is rejected', () => {
    const answer = answerDef().instantiate('answer');
    const x = place<string>('X');
    const builder = PetriNet.builder('lab')
      .compose(answer, { in: place<string>('A_IN') as Place<unknown> })
      .transition(Transition.builder('hub_kill').inputs(one(place<string>('KILL'))).reset(x).build())
      .fuse(FusionSet.of('f', answer.port('in'), x));
    expect(() => builder.build()).toThrowError(message);
  });

  it('a port retired twice keeps its first binding in the message', () => {
    const answer = answerDef().instantiate('answer');
    const builder = PetriNet.builder('lab')
      .compose(answer, { in: place<string>('H1') as Place<unknown> })
      .compose(answer, { in: place<string>('H2') as Place<unknown> })
      .transition(Transition.builder('k').inputs(one(answer.port<string>('in'))).build());
    expect(() => builder.build()).toThrowError(
      "place 'answer/IN' is port 'in' of instance 'answer', bound to host place 'H1' at compose; " +
      "reference 'H1' instead",
    );
  });

  it('a port bound to a place of the identical identity is not retired', () => {
    const answer = answerDef().instantiate('answer');
    const same = answer.port<string>('in');
    const net = PetriNet.builder('lab')
      .compose(answer, { in: same as Place<unknown> })
      .transition(Transition.builder('feed').inputs(one(place<string>('SRC'))).outputs(outPlace(same)).build())
      .build();
    expect([...net.places].some(p => p.name === 'answer/IN')).toBe(true);
  });
});

describe('PetriNet.subnetOf (MOD-040)', () => {
  it('instance composition answers the prefix, although it records no membership (MOD-026 rule 4)', () => {
    const answer = answerDef().instantiate('answer');
    const net = PetriNet.builder('lab')
      .compose(answer, { in: place<string>('A_IN') as Place<unknown> })
      .build();
    expect(net.subnetMembership.size).toBe(0);
    expect(net.subnetOf('answer/call')).toBe('answer');
    expect(net.subnetOf('answer/OUT')).toBe('answer');
    expect(net.subnetOf('A_IN')).toBeUndefined();
  });

  it('a nested prefix is everything before the last slash', () => {
    // The name a nested instance composition produces (MOD-013).
    const net = PetriNet.builder('lab')
      .transition(Transition.builder('outer/inner/call').inputs(one(place<string>('outer/inner/IN'))).build())
      .build();
    expect(net.subnetOf('outer/inner/call')).toBe('outer/inner');
    expect(instancePrefixOf('outer/inner/call')).toBe('outer/inner');
  });

  it('direct composition answers the membership entry', () => {
    const net = PetriNet.builder('Host').compose(producer()).build();
    expect(net.subnetOf('produce')).toBe('Producer');
    expect(net.subnetOf('nextItem')).toBe('Producer');
  });

  it('walks up to a prefix that owns a transition: s1/obs/TURN belongs to s1', () => {
    const net = PetriNet.builder('lab')
      .transition(Transition.builder('s1/t').inputs(one(place<string>('s1/obs/TURN'))).build())
      .build();
    expect(net.subnetOf('s1/obs/TURN')).toBe('s1');
    expect(net.subnetOf('s1/t')).toBe('s1');
    // DOT AUTO clustering is unchanged: still the part before the last slash.
    expect(instancePrefixOf('s1/obs/TURN')).toBe('s1/obs');
  });

  it('a slashed place with no transition under any of its prefixes answers undefined', () => {
    const net = PetriNet.builder('lab')
      .transition(Transition.builder('t').inputs(one(place<string>('x/y'))).build())
      .build();
    expect(net.subnetOf('x/y')).toBeUndefined();
  });

  it('a nested instance with a transition of its own is the longest match', () => {
    const net = PetriNet.builder('lab')
      .transition(Transition.builder('outer/t').inputs(one(place<string>('outer/p'))).build())
      .transition(Transition.builder('outer/inner/t').inputs(one(place<string>('outer/inner/p'))).build())
      .build();
    expect(net.subnetOf('outer/inner/p')).toBe('outer/inner');
    expect(net.subnetOf('outer/p')).toBe('outer');
  });

  it('membership still wins over the walk-up', () => {
    const net = PetriNet.builder('Host').compose(producer())
      .transition(Transition.builder('s1/t').inputs(one(place<string>('s1/obs/TURN'))).build())
      .build();
    expect(net.subnetOf('produce')).toBe('Producer');
    expect(net.subnetOf('s1/obs/TURN')).toBe('s1');
  });

  it('a leading slash is not a prefix and does not end the walk: /x/t belongs to /x', () => {
    const net = PetriNet.builder('lab')
      .transition(Transition.builder('/x/t').inputs(one(place<string>('/x/p'))).build())
      .build();
    expect(net.subnetOf('/x/t')).toBe('/x');
    expect(net.subnetOf('/x/p')).toBe('/x');
  });

  it('a name that is neither a place nor a transition answers undefined', () => {
    const answer = answerDef().instantiate('answer');
    const net = PetriNet.builder('lab').compose(answer, { in: place<string>('A_IN') as Place<unknown> }).build();
    expect(net.subnetOf('answer/IN')).toBeUndefined(); // retired by the binding
    expect(net.subnetOf('answer/nope')).toBeUndefined();
  });
});
