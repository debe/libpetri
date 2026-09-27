import { describe, it, expect } from 'vitest';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, type Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { fork, passthrough, transform } from '../../src/core/transition-action.js';
import { tokenOf } from '../../src/core/token.js';
import { deadlockFree, placeBound } from '../../src/verification/smt-property.js';
import { arrivals, bounded } from '../../src/verification/analysis/environment-analysis-mode.js';
import type { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { produces } from '../fixtures/producing-actions.js';
import { describeZ3 } from '../fixtures/z3.js';
import { FIG_13B_ROWS, pnidNet } from '../fixtures/pnid-nets.js';

/**
 * [MOD-051] `SubnetDef.verify(harness, options)`: the environment mode, the per-property
 * `configure` hook, `arrivals(k)`, and `SubnetDef.bindActions`.
 */

const reasonOf = (r: { verdict: { type: string; reason?: string }; report: string }) => {
  expect(r.verdict.type, r.report).toBe('unknown');
  return (r.verdict as { reason: string }).reason;
};

/** A subnet forwarding each token of input port `in` to output port `out`. */
function forwarder(): SubnetDef<void> {
  const input = place<string>('in');
  const out = place<string>('out');
  return SubnetDef.builder('Forward')
    .transition(Transition.builder('forward').inputs(one(input)).outputs(outPlace(out)).action(produces()).build())
    .inputPort('in', input)
    .outputPort('out', out)
    .build();
}

const harness = (properties: ReturnType<typeof placeBound>[] | ReturnType<typeof deadlockFree>[]) => ({
  params: undefined as never,
  portInputGenerators: { in: () => tokenOf('x') },
  properties,
});

const OUT = place('harness_out_out');

describe('SubnetDef.verify options (MOD-051)', () => {
  it('arrivals(k) bounds the total a port receives: placeBound(out, k) is proven (AC5)', async () => {
    const result = await forwarder().verify(harness([placeBound(OUT, 2)]), { environmentMode: arrivals(2) });
    const r = [...result.perProperty.values()][0]!;
    expect(r.verdict.type, r.report).toBe('proven');
  });

  it('a bare environment mode is still accepted as the second argument', async () => {
    const result = await forwarder().verify(harness([placeBound(OUT, 1)]), arrivals(2));
    expect([...result.perProperty.values()][0]!.verdict.type).toBe('violated');
  });

  it('a null second argument from a JavaScript caller means the default mode, as before', async () => {
    const result = await forwarder().verify(harness([placeBound(OUT, 1)]), null as never);
    expect([...result.perProperty.values()][0]!.verdict.type).not.toBe('proven');
  });

  it('configure runs once per property, after the setup, with the synthetic net (AC6)', async () => {
    const seen: string[] = [];
    const result = await forwarder().verify(harness([placeBound(OUT, 2), placeBound(OUT, 3)]), {
      environmentMode: arrivals(2),
      configure: (v: SmtVerifier, synth: PetriNet) => {
        seen.push(synth.name);
        expect([...synth.places].map(p => p.name)).toContain('harness_out_out');
        return v.totalBudget(0);
      },
    });
    expect(seen).toEqual(['verify_Forward', 'verify_Forward']);
    for (const r of result.perProperty.values()) {
      expect(reasonOf(r)).toBe('total verification budget of 0 ms exhausted during net preparation');
    }
  });

  it('a sink place named in the hook changes a quiescence verdict (AC6)', async () => {
    const stranded = await forwarder().verify(harness([deadlockFree()]), { environmentMode: arrivals(1) });
    expect([...stranded.perProperty.values()][0]!.verdict.type).toBe('violated');
    const sunk = await forwarder().verify(harness([deadlockFree()]), {
      environmentMode: arrivals(1),
      configure: (v, synth) => v.sinkPlaces([...synth.places].find(p => p.name === 'harness_out_out')!),
    });
    const r = [...sunk.perProperty.values()][0]!;
    expect(r.verdict.type, r.report).toBe('proven');
  });
});

describeZ3('SubnetDef.verify arrivals against bounded (MOD-051 AC5)', () => {
  it('bounded(k) refills the port forever: placeBound(out, k) is violated', async () => {
    const result = await forwarder().verify(harness([placeBound(OUT, 2)]), {
      environmentMode: bounded(2), configure: v => v.timeout(30_000),
    });
    const r = [...result.perProperty.values()][0]!;
    expect(r.verdict.type, r.report).toBe('violated');
  });
});

/**
 * PNID Fig. 13(b) as a subnet: `R` is the input port, fed by `arrivals(2)`. In BASE the relay `b`
 * reads as a fresh mint, so the joins never fire, `R` is never refunded, at most two cases run and
 * `B2` stays within 2: a false `proven`. With carrier `P1` in EXTENDED the joins refund `R`, every
 * case strands a `B2` token, and `B2` passes 2.
 */
function fig13bDef(): SubnetDef<void> {
  const { net, places } = pnidNet('Fig13b', FIG_13B_ROWS);
  return SubnetDef.builder('Fig13b')
    .transitions(...net.transitions)
    .inputPort('R', places.get('R')!)
    .build();
}

describe('ν options reach the per-property verifier (MOD-051 AC7)', () => {
  const B2 = place('sut/B2');
  const nuHarness = {
    params: undefined as never,
    portInputGenerators: { R: () => tokenOf('r') },
    properties: [placeBound(B2, 2)],
  };

  it('BASE (options unset) proves placeBound(sut/B2, 2) — a different model', async () => {
    const result = await fig13bDef().verify(nuHarness, { environmentMode: arrivals(2) });
    const r = [...result.perProperty.values()][0]!;
    expect(r.verdict.type, r.report).toBe('proven');
  });

  it('EXTENDED with carrier sut/P1, set through configure, violates it', async () => {
    const result = await fig13bDef().verify(nuHarness, {
      environmentMode: arrivals(2),
      configure: (v, synth) => {
        const p1 = [...synth.places].find(p => p.name === 'sut/P1')!;
        return v.fragmentMode('extended').carrierPlaces(p1).nuMaxClasses(2000);
      },
    });
    const r = [...result.perProperty.values()][0]!;
    expect(r.verdict.type, r.report).toBe('violated');
    expect(r.route).toBe('nu-scg');
  });
});

describe('SubnetDef.bindActions (MOD-051 AC8)', () => {
  const actionOf = (net: PetriNet, name: string) => [...net.transitions].find(t => t.name === name)!.action;

  it('returns a new definition whose instances carry the bound action; the receiver keeps its own', () => {
    const input = place<string>('in');
    const out = place<string>('out');
    const work = Transition.builder('work').inputs(one(input)).outputs(outPlace(out)).build();
    const old = SubnetDef.builder('Bind')
      .transition(work)
      .inputPort('in', input)
      .outputPort('out', out)
      .channel('go', work)
      .build();
    const action = fork();
    const bound = old.bindActions({ work: action });

    expect(bound).not.toBe(old);
    expect(actionOf(bound.instantiate('n').renamedBody, 'n/work')).toBe(action);
    expect(actionOf(old.instantiate('o').renamedBody, 'o/work')).toBe(passthrough());
    expect([...bound.iface.ports.keys()]).toEqual(['in', 'out']);
    expect(bound.iface.ports.get('out')!.place).toBe(out as Place<unknown>);
    // The channel follows the rebound transition.
    expect(bound.iface.channels.get('go')!.transition.action).toBe(action);
    expect(old.iface.channels.get('go')!.transition.action).toBe(passthrough());
  });

  it('the resolver form defers a transition on null, as at net level (CORE-042)', () => {
    const input = place<string>('in');
    const out = place<string>('out');
    const first = transform(() => null);
    const def0 = SubnetDef.builder('Stage')
      .transition(Transition.builder('work').inputs(one(input)).outputs(outPlace(out)).action(first).build())
      .transition(Transition.builder('other').inputs(one(out)).build())
      .inputPort('in', input)
      .build();
    const second = fork();
    const bound = def0.bindActionsWithResolver(n => (n === 'other' ? second : null));
    expect(actionOf(bound.body, 'work')).toBe(first);
    expect(actionOf(bound.body, 'other')).toBe(second);
    // The map form substitutes passthrough for what it omits (CORE-042 divergence note).
    expect(actionOf(def0.bindActions({ other: second }).body, 'work')).toBe(passthrough());
  });

  it('verify still applies CORE-043 to the bound definition', async () => {
    const bound = forwarder().bindActions({});
    await expect(bound.verify(harness([placeBound(OUT, 1)]))).rejects.toThrow(/forward/);
  });

});
