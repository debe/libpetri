import { describe, it, expect } from 'vitest';
import { Interface } from '../../src/core/interface.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import type { Port } from '../../src/core/interface.js';

describe('Interface', () => {
  it('port discriminated direction is preserved through accessors', () => {
    const p = place<string>('p');
    const iface = Interface.builder()
      .inputPort('in', p)
      .outputPort('out', p)
      .inoutPort('io', p)
      .build();

    function classify(port: Port<unknown>): string {
      switch (port.direction) {
        case 'input': return `Input(${port.name})`;
        case 'output': return `Output(${port.name})`;
        case 'inout': return `InOut(${port.name})`;
        default: {
          const _exhaustive: never = port.direction;
          return _exhaustive;
        }
      }
    }

    expect(classify(iface.port('in')!)).toBe('Input(in)');
    expect(classify(iface.port('out')!)).toBe('Output(out)');
    expect(classify(iface.port('io')!)).toBe('InOut(io)');
  });

  it('channel retrievable by name', () => {
    const p = place<string>('p');
    const t = Transition.builder('attempt').read(p).build();
    const iface = Interface.builder()
      .channel('attempt', t)
      .build();

    const resolved = iface.channel('attempt');
    expect(resolved).toBeDefined();
    expect(resolved?.transition).toBe(t);
  });

  it('placeAs returns undefined on missing name', () => {
    const iface = Interface.builder().build();
    expect(iface.placeAs<string>('nope')).toBeUndefined();
  });

  it('placeAs returns the underlying place on match', () => {
    const stringPlace = place<string>('s');
    const iface = Interface.builder()
      .inputPort('in', stringPlace)
      .build();

    const resolved = iface.placeAs<string>('in');
    expect(resolved).toBe(stringPlace);
  });

  it('builder rejects duplicate port name within port namespace', () => {
    const p1 = place<string>('p1');
    const p2 = place<string>('p2');

    expect(() =>
      Interface.builder()
        .inputPort('dup', p1)
        .outputPort('dup', p2)
        .build(),
    ).toThrow(/dup/);
  });

  it('builder rejects duplicate channel name within channel namespace', () => {
    const p = place<string>('p');
    const t1 = Transition.builder('t1').read(p).build();
    const t2 = Transition.builder('t2').read(p).build();

    expect(() =>
      Interface.builder()
        .channel('ch', t1)
        .channel('ch', t2)
        .build(),
    ).toThrow(/ch/);
  });

  it('Symbol-guarded constructor rejects direct instantiation', () => {
    expect(() =>
      new Interface(Symbol('imposter'), new Map(), new Map()),
    ).toThrow(/Use Interface\.builder/);
  });

  it('port and channel maps are populated in declaration order', () => {
    const p1 = place<string>('p1');
    const p2 = place<string>('p2');
    const iface = Interface.builder()
      .inputPort('first', p1)
      .outputPort('second', p2)
      .build();

    expect([...iface.ports.keys()]).toEqual(['first', 'second']);
  });
});
