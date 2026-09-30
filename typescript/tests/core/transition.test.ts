import { describe, it, expect } from 'vitest';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one, exactly, type In } from '../../src/core/in.js';
import { matchKey, matchSpec } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { xorPlaces, andPlaces, outPlace, forwardInput, timeout } from '../../src/core/out.js';
import { delayed, MAX_DURATION_MS, type Timing } from '../../src/core/timing.js';

describe('Transition', () => {
  const p1 = place<string>('P1');
  const p2 = place<number>('P2');
  const p3 = place<string>('P3');
  const p4 = place<string>('P4');

  it('creates with builder', () => {
    const t = Transition.builder('MyTransition')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();

    expect(t.name).toBe('MyTransition');
    expect(t.inputSpecs).toHaveLength(1);
    expect(t.outputSpec).not.toBeNull();
  });

  it('collects input places', () => {
    const t = Transition.builder('T')
      .inputs(one(p1), exactly(2, p2))
      .build();

    expect(t.inputPlaces().size).toBe(2);
  });

  it('collects output places from AND', () => {
    const t = Transition.builder('T')
      .outputs(andPlaces(p1, p2))
      .build();

    expect(t.outputPlaces().size).toBe(2);
  });

  it('collects output places from XOR', () => {
    const t = Transition.builder('T')
      .outputs(xorPlaces(p1, p2))
      .build();

    expect(t.outputPlaces().size).toBe(2);
  });

  it('sets timing', () => {
    const t = Transition.builder('T')
      .timing(delayed(500))
      .build();

    expect(t.timing.type).toBe('delayed');
  });

  it('sets priority', () => {
    const t = Transition.builder('T')
      .priority(10)
      .build();

    expect(t.priority).toBe(10);
  });

  it('defaults to immediate timing', () => {
    const t = Transition.builder('T').build();
    expect(t.timing.type).toBe('immediate');
  });

  it('defaults to passthrough action', () => {
    const t = Transition.builder('T').build();
    expect(t.action).toBeDefined();
  });

  it('adds inhibitor', () => {
    const t = Transition.builder('T')
      .inhibitor(p1)
      .build();

    expect(t.inhibitors).toHaveLength(1);
    expect(t.inhibitors[0]!.place).toBe(p1);
  });

  it('adds read', () => {
    const t = Transition.builder('T')
      .read(p1)
      .build();

    expect(t.reads).toHaveLength(1);
    expect(t.readPlaces().size).toBe(1);
  });

  it('adds reset', () => {
    const t = Transition.builder('T')
      .reset(p1)
      .build();

    expect(t.resets).toHaveLength(1);
  });

  it('detects action timeout in output spec', () => {
    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(xorPlaces(p3, p4))
      .build();

    expect(t.hasActionTimeout()).toBe(false);

    const t2 = Transition.builder('T2')
      .inputs(one(p1))
      .outputs(timeout(5000, outPlace(p3)))
      .build();

    expect(t2.hasActionTimeout()).toBe(true);
    expect(t2.actionTimeout!.afterMs).toBe(5000);
  });

  it('validates ForwardInput references input place', () => {
    expect(() => {
      Transition.builder('T')
        .inputs(one(p1))
        .outputs(forwardInput(p2, p3)) // p2 is NOT an input
        .build();
    }).toThrow('non-input place');
  });

  it('ForwardInput with valid input place succeeds', () => {
    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(timeout(5000, forwardInput(p1, p3)))
      .build();

    expect(t.outputPlaces().size).toBe(1);
  });

  it('uses identity-based equality', () => {
    const t1 = Transition.builder('T').build();
    const t2 = Transition.builder('T').build();
    expect(t1).not.toBe(t2);
  });

  it('toString', () => {
    const t = Transition.builder('MyT').build();
    expect(t.toString()).toBe('Transition[MyT]');
  });
});

describe('arcs the helpers reject, written out directly (IO-002, IO-004, NU-020)', () => {
  const a = place<string>('A');
  const b = place<string>('B');
  const merged = place<string>('merged');
  const key = (v: string) => nameId(v);

  it('matchSpec rejects a place keyed twice', () => {
    expect(() => matchSpec(matchKey(a, key), matchKey(a, key))).toThrow(
      "MatchSpec correlates input place 'A' twice",
    );
  });

  it('build rejects a place keyed twice in a literal spec', () => {
    expect(() =>
      Transition.builder('join')
        .inputs(one(a), one(b))
        .match({ keys: [matchKey(a, key), matchKey(a, key)] })
        .outputs(outPlace(merged))
        .build(),
    ).toThrow("MatchSpec correlates input place 'A' twice");
  });

  it('build rejects an input that requires no token', () => {
    const zero: In[] = [
      { type: 'exactly', place: b, count: 0 },
      { type: 'at-least', place: b, minimum: 0 },
    ];
    for (const spec of zero) {
      expect(() =>
        Transition.builder('join')
          .inputs(one(a), spec)
          .match(matchSpec(matchKey(a, key), matchKey(b, key)))
          .outputs(outPlace(merged))
          .build(),
      ).toThrow("input 'B' of transition 'join' requires 0 tokens");
    }
  });
});

describe('timings the factories reject, written out directly (TIME-001 AC5)', () => {
  const t = (timing: Timing) => Transition.builder('t').timing(timing).build();

  it('build rejects each invalid literal with the factory message', () => {
    const cases: [Timing, string][] = [
      [{ type: 'delayed', afterMs: MAX_DURATION_MS + 1 }, 'Delay must be at most MAX_DURATION_MS'],
      [{ type: 'delayed', afterMs: -1 }, 'Delay must be non-negative'],
      [
        { type: 'window', earliestMs: MAX_DURATION_MS + 1, latestMs: MAX_DURATION_MS + 2 },
        'Earliest must be at most MAX_DURATION_MS',
      ],
      [{ type: 'window', earliestMs: 5, latestMs: 3 }, 'Latest (3) must be >= earliest (5)'],
      [{ type: 'exact', atMs: MAX_DURATION_MS + 1 }, 'Exact time must be at most MAX_DURATION_MS'],
      [{ type: 'deadline', byMs: 0 }, 'Deadline must be positive: 0'],
    ];
    for (const [timing, message] of cases) {
      expect(() => t(timing)).toThrow(message);
    }
  });

  it('build accepts a valid literal', () => {
    const valid: Timing[] = [
      { type: 'immediate' },
      { type: 'deadline', byMs: 1 },
      { type: 'delayed', afterMs: MAX_DURATION_MS },
      { type: 'window', earliestMs: MAX_DURATION_MS, latestMs: MAX_DURATION_MS },
      { type: 'exact', atMs: MAX_DURATION_MS },
    ];
    for (const timing of valid) {
      expect(t(timing).timing).toEqual(timing);
    }
  });
});
