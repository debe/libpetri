/**
 * The TS sensors must reproduce the net-metrics lab (research/net-metrics/lab/results/*.jsonl).
 * Expected values below are copied from those files; the round is named on each block.
 */
import { describe, expect, it } from 'vitest';
import { analysisAlwaysAvailable, z3Available } from 'libpetri/verification';
import type { PetriNet } from 'libpetri';
import {
  boundedness,
  changeImpact,
  encapsulationViolations,
  environmentSources,
  markingOf,
  measure,
  probeUntimed,
  resetSensors,
  wlSymmetry,
} from '../src/sensors.js';
import { bindStructureOnly } from '../src/net-utils.js';
import {
  cancelDrains, cancelReset, conflictPair, FIXTURES, gatherNu, gatherSlots, keptLatch, readCanceller,
  resetToConsume, session, turns, watchdogs,
} from './fixtures.js';

type Built = { net: PetriNet; marking: ReadonlyMap<string, number> };
const HAS_Z3 = z3Available();
const KS = [1, 2, 3, 4];

const classes = (b: Built, maxClasses?: number) => {
  const net = bindStructureOnly(b.net);
  return probeUntimed(net, markingOf(net, b.marking), new Set(), { maxClasses });
};
const bounds = (b: Built) => boundedness(bindStructureOnly(b.net));

describe('r1: cancel family (Families.cancelReset / cancelDrains)', () => {
  const lab = {
    reset: { blast: [3, 5, 7, 9], reach: [3, 4, 5, 6], classes: [5, 7, 11, 19], wlSym: [0, 0.4, 0.5, 0.571] },
    drains: { blast: [0, 0, 0, 0], reach: [0, 0, 0, 0], classes: [9, 17, 39, 101], wlSym: [0, 0.545, 0.643, 0.706] },
  };
  for (const [variant, build] of [['reset', cancelReset], ['drains', cancelDrains]] as const) {
    it(`${variant}: resetBlast, resetReach, classes, wlSym at k = 1..4`, () => {
      KS.forEach((k, i) => {
        const b = build(k);
        const r = resetSensors(b.net);
        expect(r.blast, `k=${k}`).toBe(lab[variant].blast[i]);
        expect(r.reach, `k=${k}`).toBe(lab[variant].reach[i]);
        expect(classes(b).classes, `k=${k}`).toBe(lab[variant].classes[i]);
        // wlSymUndeclared = wlSym here: no subnet instances
        expect(wlSymmetry(b.net, 3, true), `k=${k}`).toBe(lab[variant].wlSym[i]);
      });
    });
  }

  it.skipIf(!HAS_Z3)('both variants are structurally bounded, no essential power arc', async () => {
    for (const b of [cancelReset(3), cancelDrains(3)]) expect(await bounds(b)).toEqual({ essentialPowerArcs: 0, boundedFraction: 1 });
  });

  it('measure(): stateGrowth is classes at k = 1, 2 and their ratio', async () => {
    const m = await measure(FIXTURES.cancelReset.contract, FIXTURES.cancelReset.candidate);
    expect(m.stateGrowth).toEqual({ k1: 5, k2: 7, multiplier: 1.4 });
    expect(m.size).toEqual({ places: 6, transitions: 4, arcs: 13 });
    expect(m.routes).toEqual({ ordinary: false, enumerable: true, nu: false, timed: false });
    const d = await measure(FIXTURES.cancelDrains.contract, FIXTURES.cancelDrains.candidate);
    expect(d.stateGrowth).toEqual({ k1: 9, k2: 17, multiplier: 1.889 });
  });

  it('changeImpact: growing the cancel family edits fork, join and abort (r1 changeImpact 3)', () => {
    expect(changeImpact(cancelReset(1).net, cancelReset(2).net).changed).toEqual(['abort', 'fork', 'join']);
    expect(changeImpact(cancelDrains(1).net, cancelDrains(2).net).changed).toHaveLength(3);
  });
});

describe('r4/r9: subnet session, local cleanup vs hub reset (instantiate + prefix membership)', () => {
  it('hub: resetBlast 2F, resetReach 2F+1, crossReset F, encapViolations F; local all 0', () => {
    for (const F of KS) {
      const hub = session(F, false).net;
      expect(resetSensors(hub)).toEqual({ count: 2 * F, blast: 2 * F, reach: 2 * F + 1, crossSubnet: F });
      expect(encapsulationViolations(hub)).toBe(F);
      const local = session(F, true).net;
      expect(resetSensors(local)).toEqual({ count: 0, blast: 0, reach: 0, crossSubnet: 0 });
      expect(encapsulationViolations(local)).toBe(0);
    }
  });

  it('r10: wlSymUndeclared is 0 for instantiated stages while raw wlSym sees the copies', () => {
    const raw = { local: [0, 0.5, 0.643, 0.722], hub: [0, 0.5, 0.625, 0.7] };
    KS.forEach((F, i) => {
      for (const v of ['local', 'hub'] as const) {
        const net = session(F, v === 'local').net;
        expect(wlSymmetry(net, 3, false), `${v} F=${F}`).toBe(raw[v][i]);
        expect(wlSymmetry(net, 3, true), `${v} F=${F}`).toBe(0);
      }
    });
  });

  it('classes match the lab (local 8/12/16/20, hub 9/13/17/21)', () => {
    KS.forEach((F, i) => {
      expect(classes(session(F, true)).classes).toBe([8, 12, 16, 20][i]);
      expect(classes(session(F, false)).classes).toBe([9, 13, 17, 21][i]);
    });
  });

  it('changeImpact per added stage: local 1, hub 2 (r6 finding 4)', () => {
    for (const F of [1, 2, 3]) {
      expect(changeImpact(session(F, true).net, session(F + 1, true).net).changed).toHaveLength(1);
      const hub = changeImpact(session(F, false).net, session(F + 1, false).net).changed;
      expect(hub).toHaveLength(2);
      expect(hub).toContain('barge_in'); // the reset hub is edited on every feature
    }
  });

  it.skipIf(!HAS_Z3)('both variants bounded (essentialPower 0, boundedFrac 1)', async () => {
    for (const b of [session(3, true), session(3, false)]) expect(await bounds(b)).toEqual({ essentialPowerArcs: 0, boundedFraction: 1 });
  });

  it('measure() on the hub reads the k = 1 structure', async () => {
    const m = await measure(FIXTURES.sessionHub.contract, FIXTURES.sessionHub.candidate);
    expect(m.resets).toMatchObject({ count: 2, blast: 2, reach: 3, crossSubnet: 1, multiToken: 0 });
    expect(m.encapsulationViolations).toBe(1);
    expect(m.stateGrowth).toEqual({ k1: 9, k2: 13, multiplier: 1.444 });
  });
});

describe('r6/r9: event turns, consume vs reset (EnvNets.turns, arrival generator)', () => {
  const lab = {
    consume: { blast: [0, 0, 0, 0], reach: [0, 0, 0, 0], classes: [9, 12, 15, 18], wl: [0, 0, 0, 0.2] },
    reset: { blast: [1, 2, 3, 4], reach: [2, 3, 4, 5], classes: [11, 15, 19, 23], wl: [0, 0, 0, 0] },
  } as const;
  for (const mode of ['consume', 'reset'] as const) {
    it(`${mode}: blast, reach, classes, wlSymUndeclared at s = 1..4`, () => {
      KS.forEach((s, i) => {
        const b = turns(s, mode);
        const r = resetSensors(b.net);
        expect(r.blast).toBe(lab[mode].blast[i]);
        expect(r.reach).toBe(lab[mode].reach[i]);
        expect(classes(b).classes).toBe(lab[mode].classes[i]);
        expect(wlSymmetry(b.net, 3, true)).toBe(lab[mode].wl[i]);
      });
    });
  }

  it('changeImpact per added stage: consume 1, reset 2', () => {
    for (const s of [1, 2, 3]) {
      expect(changeImpact(turns(s, 'consume').net, turns(s + 1, 'consume').net).changed).toEqual(['finish']);
      expect(changeImpact(turns(s, 'reset').net, turns(s + 1, 'reset').net).changed).toEqual(['barge', 'finish']);
    }
  });

  it('an arrival generator supply (marked SOURCE) is not an environment place: enumerable stays true', async () => {
    const m = await measure(FIXTURES.turnsReset.contract, FIXTURES.turnsReset.candidate);
    expect(m.routes.enumerable).toBe(true);
    expect(m.stateGrowth).toEqual({ k1: 11, k2: 15, multiplier: 1.364 });
  });
});

describe('r7: environment place INBOX (EnvNets.envTurns)', () => {
  it.skipIf(!HAS_Z3)('essentialPower / boundedFrac: consume 0/0.5, reset 2/0.0, idleInhib 1/0.6', async () => {
    const lab = { envTurnsConsume: [0, 0.5], envTurnsReset: [2, 0], envTurnsIdle: [1, 0.6] } as const;
    for (const [name, [ep, bf]] of Object.entries(lab)) {
      const f = FIXTURES[name as keyof typeof lab];
      const m = await measure(f.contract, f.candidate);
      expect(m.essentialPowerArcs, name).toBe(ep);
      expect(m.boundedFraction, name).toBe(bf);
      expect(m.routes.enumerable, name).toBe(false);
    }
  });

  it('with injection the graph never closes (lab: -200000): negative classes, multiToken -1, cap configurable', () => {
    const f = FIXTURES.envTurnsReset;
    const b = f.candidate.build(1);
    const net = bindStructureOnly(b.net);
    const env = environmentSources(f.contract, net, b.marking);
    expect([...env].map(e => e.place.name)).toEqual(['INBOX']);
    const p = probeUntimed(net, markingOf(net, b.marking), env, { maxClasses: 500, envMode: analysisAlwaysAvailable() });
    expect(p.classes).toBeLessThan(0);
    expect(p.multiToken).toBe(-1);
  });
});

describe('r14: §15 fixes (human-labelled pairs)', () => {
  const multi = (b: Built) => classes(b).multiToken;

  it('multiReset flags resetToConsume and readCanceller only at k >= 2, never keptLatch', () => {
    expect([1, 2, 3].map(k => multi(resetToConsume(k, false)))).toEqual([0, 1, 1]);
    expect([1, 2, 3].map(k => multi(readCanceller(k, false)))).toEqual([0, 2, 2]);
    expect([1, 2, 3].map(k => multi(keptLatch(k)))).toEqual([0, 0, 0]);
    expect([1, 2, 3].map(k => multi(conflictPair(k, false)))).toEqual([0, 0, 0]);
    for (const k of [1, 2, 3]) {
      expect(multi(resetToConsume(k, true))).toBe(0);
      expect(multi(readCanceller(k, true))).toBe(0);
    }
  });

  it('measure() reads multiToken at k = 2', async () => {
    const r = async (f: keyof typeof FIXTURES) => (await measure(FIXTURES[f].contract, FIXTURES[f].candidate)).resets.multiToken;
    expect(await r('resetToConsumeBefore')).toBe(1);
    expect(await r('readCancellerBefore')).toBe(2);
    expect(await r('keptLatch')).toBe(0);
    expect(await r('resetToConsumeAfter')).toBe(0);
  });

  it('classes match the lab at k = 1..3', () => {
    expect([1, 2, 3].map(k => classes(resetToConsume(k, false)).classes)).toEqual([2, 5, 9]);
    expect([1, 2, 3].map(k => classes(resetToConsume(k, true)).classes)).toEqual([2, 3, 4]);
    expect([1, 2, 3].map(k => classes(readCanceller(k, false)).classes)).toEqual([5, 9, 14]);
    expect([1, 2, 3].map(k => classes(readCanceller(k, true)).classes)).toEqual([4, 7, 11]);
    expect([1, 2, 3].map(k => classes(conflictPair(k, true)).classes)).toEqual([3, 4, 5]);
    expect([1, 2, 3].map(k => classes(keptLatch(k)).classes)).toEqual([2, 2, 2]);
  });

  it.skipIf(!HAS_Z3)('essentialPower: 1 for resetToConsume-before, 0 after, 2 for keptLatch (an inhibitor-guarded producer bounds nothing while in flight)', async () => {
    expect(await bounds(resetToConsume(1, false))).toEqual({ essentialPowerArcs: 1, boundedFraction: 0.667 });
    expect(await bounds(resetToConsume(1, true))).toEqual({ essentialPowerArcs: 0, boundedFraction: 1 });
    // work's inhibitor on DIRTY stays open while work is in flight (VER-004), so DIRTY is not bounded.
    expect(await bounds(keptLatch(1))).toEqual({ essentialPowerArcs: 2, boundedFraction: 0.667 });
    expect(await bounds(conflictPair(2, false))).toEqual({ essentialPowerArcs: 0, boundedFraction: 1 });
    expect(await bounds(readCanceller(2, false))).toEqual({ essentialPowerArcs: 0, boundedFraction: 1 });
  });
});

describe('r3/r10: scatter-gather, ν join vs cloned slots', () => {
  it('wlSymUndeclared: slots 0.5 at k = 1 then 1.0; ν stays 0.5 (the r10 parallel-branch false positive)', () => {
    KS.forEach((k, i) => {
      expect(wlSymmetry(gatherSlots(k).net, 3, true)).toBe([0.5, 1, 1, 1][i]);
      expect(wlSymmetry(gatherNu(k).net, 3, true)).toBe(0.5);
    });
  });

  it('structure: ν constant (P 8, T 4), slots grow 5k+2 / 4k', async () => {
    const nu = await measure(FIXTURES.gatherNu.contract, FIXTURES.gatherNu.candidate);
    expect(nu.size).toEqual({ places: 8, transitions: 4, arcs: 14 });
    expect(nu.routes).toEqual({ ordinary: true, enumerable: false, nu: true, timed: false });
    expect(FIXTURES.gatherNu.budgets).toEqual(['BUDGET']);
    const slots = await measure(FIXTURES.gatherSlots.contract, FIXTURES.gatherSlots.candidate);
    expect(slots.routes.nu).toBe(false);
    expect(slots.undeclaredSymmetry).toBe(0.5);
  });

  it('classes (plain untimed SCG, names ignored): ν 16/34/50/50, slots 16/60/200/500', () => {
    KS.forEach((k, i) => {
      expect(classes(gatherNu(k)).classes).toBe([16, 34, 50, 50][i]);
      expect(classes(gatherSlots(k)).classes).toBe([16, 60, 200, 500][i]);
    });
  });

  it('truncation is reported as a negative count and a negative multiplier', async () => {
    const m = await measure(FIXTURES.gatherSlots.contract, FIXTURES.gatherSlots.candidate, { maxClasses: 20 });
    expect(m.stateGrowth.k1).toBe(16);
    expect(m.stateGrowth.k2).toBeLessThan(0);
    expect(m.stateGrowth.multiplier).toBeLessThan(0);
  });
});

describe('r8: timed width (TimedNets.watchdogs)', () => {
  it('untimed classes 4^n; timedWidth = 2n; route timed', async () => {
    expect([1, 2, 3].map(n => classes(watchdogs(n)).classes)).toEqual([4, 16, 64]);
    expect([1, 2, 3].map(n => classes(watchdogs(n)).timedWidth)).toEqual([2, 4, 6]);
    const m = await measure(FIXTURES.watchdogs.contract, FIXTURES.watchdogs.candidate);
    expect(m.timedWidth).toBe(2);
    expect(m.routes).toEqual({ ordinary: true, enumerable: false, nu: false, timed: true });
  });
});

describe('z3 unavailable', () => {
  it('essentialPowerArcs and boundedFraction are -1, measure does not throw', async () => {
    const saved = process.env.LIBPETRI_Z3;
    process.env.LIBPETRI_Z3 = '/nonexistent/z3';
    try {
      expect(await bounds(keptLatch(1))).toEqual({ essentialPowerArcs: -1, boundedFraction: -1 });
      const m = await measure(FIXTURES.keptLatch.contract, FIXTURES.keptLatch.candidate);
      expect(m.essentialPowerArcs).toBe(-1);
      expect(m.boundedFraction).toBe(-1);
    } finally {
      if (saved === undefined) delete process.env.LIBPETRI_Z3; else process.env.LIBPETRI_Z3 = saved;
    }
  });
});
