import { describe, expect, it } from 'vitest';
import {
  PetriNet, SubnetDef, Transition, andPlaces, delayed, matchKey, matchSpec, nameId, one, outPlace, place, window,
  xorPlaces, type Place,
} from 'libpetri';
import { inFlightTransitions, z3Available } from 'libpetri/verification';
import { UNITS_ROUTE, checkUnits, lint, runGates } from '../src/gates.js';
import { analyseUnits } from '../src/units.js';
import { bindStructureOnly } from '../src/net-utils.js';
import { voiceStep5Contract, voiceStep5Minimal } from './fixtures-voice-step5.js';
import type { Candidate, Contract, GateReport, NamedProperty, PropertyResult } from '../src/types.js';

const Z3 = z3Available();
const itZ3 = Z3 ? it : it.skip;

// ─── fixture helpers ────────────────────────────────────────────────────────

type Arcs = {
  in?: Place<any>[]; out?: Place<any>[]; xor?: Place<any>[];
  reset?: Place<any>[]; inhibit?: Place<any>[]; read?: Place<any>[];
};
function tr(name: string, a: Arcs, build?: (b: ReturnType<typeof Transition.builder>) => void): Transition {
  const b = Transition.builder(name);
  if (a.in?.length) b.inputs(...a.in.map(p => one(p)));
  if (a.out?.length) b.outputs(a.out.length === 1 ? outPlace(a.out[0]!) : andPlaces(...a.out));
  if (a.xor?.length) b.outputs(xorPlaces(...a.xor));
  if (a.reset?.length) b.resets(...a.reset);
  if (a.inhibit?.length) b.inhibitors(...a.inhibit);
  if (a.read?.length) b.reads(...a.read);
  build?.(b);
  return b.build();
}
function net(name: string, ...ts: Transition[]): PetriNet {
  const b = PetriNet.builder(name);
  for (const t of ts) b.transition(t);
  return b.build();
}
function candidate(name: string, build: Candidate['build'], subnets?: Candidate['subnets']): Candidate {
  return { name, rationale: 'fixture', build, ...(subnets ? { subnets } : {}) };
}
const P = (name: string) => place<unknown>(name);
const prop = (name: string, spec: NamedProperty['spec'], timingDependent?: boolean): NamedProperty =>
  ({ name, spec, ...(timingDependent ? { timingDependent } : {}) });
function result(r: GateReport, k: number, property: string): PropertyResult {
  const s = r.smallScope.find(x => x.k === k);
  const res = s?.results.find(x => x.property === property);
  if (!res) throw new Error(`no result for ${property} at k=${k}: ${JSON.stringify(r.smallScope)}`);
  return res;
}

// ─── fixtures ───────────────────────────────────────────────────────────────

/** One-at-a-time worker: SOURCE(k) → arrive → INBOX → start → BUSY → finish → DONE (+ IDLE back). */
function worker(opts: { resetInbox?: boolean; ghostInhibitor?: boolean } = {}): Candidate {
  return candidate(opts.resetInbox ? 'resetInbox' : opts.ghostInhibitor ? 'ghost' : 'worker', k => {
    const [SOURCE, INBOX, IDLE, BUSY, DONE] = ['SOURCE', 'INBOX', 'IDLE', 'BUSY', 'DONE'].map(P) as Place<any>[];
    const n = net('worker',
      tr('arrive', { in: [SOURCE!], out: [INBOX!] }),
      tr('start', { in: [INBOX!, IDLE!], out: [BUSY!], ...(opts.ghostInhibitor ? { inhibit: [P('answer/IN')] } : {}) }),
      tr('finish', { in: [BUSY!], out: [DONE!, IDLE!], ...(opts.resetInbox ? { reset: [INBOX!] } : {}) }),
    );
    return { net: n, marking: new Map([['SOURCE', k], ['IDLE', 1]]) };
  });
}
const workerContract: Contract = {
  name: 'worker', intent: 'answer every event', sinks: ['DONE', 'IDLE'], sources: ['SOURCE'],
  properties: [
    prop('no stranded token', { kind: 'deadlockFree' }),
    prop('every event answered', { kind: 'accounting', outcomes: ['DONE'] }),
    prop('one at a time', { kind: 'placeBound', place: 'BUSY', bound: 1 }),
    prop('busy xor idle', { kind: 'mutualExclusion', a: 'BUSY', b: 'IDLE' }),
    prop('never busy and idle', { kind: 'unreachable', places: ['BUSY', 'IDLE'] }),
  ],
};

/** Guard hub (lab round 12, simplified): a failing guard resets the answer's input, but not its draft. */
const guardHub = candidate('guardHub', k => {
  const [SOURCE, INBOX, G_IN, A_IN, PASS, FAIL, DRAFT, SENT, REFUSED] =
    ['SOURCE', 'INBOX', 'G_IN', 'A_IN', 'PASS', 'FAIL', 'DRAFT', 'SENT', 'REFUSED'].map(P) as Place<any>[];
  const n = net('guardHub',
    tr('arrive', { in: [SOURCE!], out: [INBOX!] }),
    tr('fork', { in: [INBOX!], out: [G_IN!, A_IN!] }),
    tr('guard', { in: [G_IN!], xor: [PASS!, FAIL!] }),
    tr('answer', { in: [A_IN!], out: [DRAFT!] }),
    tr('send', { in: [PASS!, DRAFT!], out: [SENT!] }),
    tr('refuse', { in: [FAIL!], out: [REFUSED!], reset: [A_IN!] }),
  );
  return { net: n, marking: new Map([['SOURCE', k]]) };
});
const guardContract: Contract = {
  name: 'guard', intent: 'send or refuse every turn', sinks: ['SENT', 'REFUSED'], sources: ['SOURCE'],
  properties: [
    prop('no stranded token', { kind: 'deadlockFree' }),
    prop('every turn answered', { kind: 'accounting', outcomes: ['SENT', 'REFUSED'] }),
  ],
};

/** A two-place stage subnet: in → start → busy → finish → out. */
function stageDef(): SubnetDef<void> {
  const i = P('in'), busy = P('busy'), o = P('out');
  return SubnetDef.builder('Stage')
    .place(i).place(busy).place(o)
    .transition(tr('start', { in: [i], out: [busy] }))
    .transition(tr('finish', { in: [busy], out: [o] }))
    .inputPort('in', i).outputPort('out', o)
    .build();
}

// ─── tests ──────────────────────────────────────────────────────────────────

describe('small-scope gate (enumeration, no z3 needed)', () => {
  it('finds the guard-hub stranded draft at k = 1 with a trace; accounting stays green (r12)', async () => {
    const r = await runGates(guardContract, guardHub);
    const dl = result(r, 1, 'no stranded token');
    expect(dl.verdict).toBe('violated');
    expect(dl.route).toBe('enumeration');
    expect(dl.trace).toBeDefined();
    expect(dl.trace).toContain('refuse');
    expect(dl.trace).toContain('answer');
    expect(result(r, 1, 'every turn answered').verdict).toBe('proven');
    expect(r.passed).toBe(false);
  });

  it('reset on the inbox: deadlockFree proven, accounting violated at k = 2 (r6, r15)', async () => {
    const r = await runGates(workerContract, worker({ resetInbox: true }));
    for (const k of [1, 2]) expect(result(r, k, 'no stranded token').verdict).toBe('proven');
    expect(result(r, 1, 'every event answered').verdict).toBe('proven');
    const acc = result(r, 2, 'every event answered');
    expect(acc.verdict).toBe('violated');
    expect(acc.trace?.length).toBeGreaterThan(0);
    expect(r.lint.some(f => f.rule === 'reset-on-source-fed' && f.place === 'INBOX' && f.severity === 'warning')).toBe(true);
    expect(r.passed).toBe(false);
  });

  it('passes a correct design on every property at k = 1, 2', async () => {
    const r = await runGates(workerContract, worker());
    expect(r.lint).toEqual([]);
    for (const s of r.smallScope) for (const res of s.results) {
      expect(res.verdict, `${res.property} @k=${s.k}: ${res.note}`).toBe('proven');
    }
    expect(r.smallScope.map(s => s.k)).toEqual([1, 2]);
    expect(r.passed).toBe(true);
  });

  it('reports a property naming a missing place as a contract error, not a pass', async () => {
    const contract: Contract = { ...workerContract, properties: [prop('typo', { kind: 'placeBound', place: 'BUSSY', bound: 1 })] };
    const r = await runGates(contract, worker());
    const res = result(r, 1, 'typo');
    expect(res.verdict).toBe('unknown');
    expect(res.route).toBe('contract');
    expect(res.note).toMatch(/contract error.*BUSSY/);
    expect(r.passed).toBe(false);
  });

  itZ3('reports an untimed counterexample spurious under timing as not violated (r8, VER-023)', async () => {
    // Lab round 8, timing variant: answer (window [0, 2]) and watchdog (delayed 5) race for CALLING.
    const c = candidate('watchdog', () => {
      const [REQ, CALLING, RESP, TIMEOUT] = ['REQ', 'CALLING', 'RESP', 'TIMEOUT'].map(P) as Place<any>[];
      const n = net('watchdog',
        tr('start', { in: [REQ!], out: [CALLING!] }),
        tr('answer', { in: [CALLING!], out: [RESP!] }, b => b.timing(window(0, 2))),
        tr('watchdog', { in: [CALLING!], out: [TIMEOUT!] }, b => b.timing(delayed(5))),
      );
      return { net: n, marking: new Map([['REQ', 1]]) };
    });
    const contract: Contract = {
      name: 'watchdog', intent: 'no call times out', sinks: ['RESP', 'TIMEOUT'], sources: ['REQ'],
      properties: [prop('never times out', { kind: 'unreachable', places: ['TIMEOUT'] }, true)], scales: [1],
    };
    const res = result(await runGates(contract, c), 1, 'never times out');
    expect(res.route).toBe('timed-scg');
    expect(res.verdict).toBe('proven');
    expect(res.note).toMatch(/spurious under timing/);
  });
});

describe('lint', () => {
  const empty = new Map<string, number>();
  const bare: Contract = { name: 'c', intent: '', properties: [], sinks: [], sources: [] };

  it('flags a dead power arc as an error, and the gate fails on it', async () => {
    const r = await runGates(workerContract, worker({ ghostInhibitor: true }));
    const f = r.lint.find(x => x.rule === 'dead-power-arc');
    expect(f).toMatchObject({ severity: 'error', transition: 'start', place: 'answer/IN' });
    for (const s of r.smallScope) for (const res of s.results) expect(res.verdict).toBe('proven');
    expect(r.passed).toBe(false);
  });

  it('does not flag a power arc on a place that is produced, consumed or initially marked', () => {
    const [A, B, L] = ['A', 'B', 'L'].map(P) as Place<any>[];
    const n = net('n', tr('t', { in: [A!], out: [B!], inhibit: [B!], read: [L!] }));
    expect(lint(n, new Map([['L', 1]]), bare).filter(f => f.rule === 'dead-power-arc')).toEqual([]);
  });

  it('two input specs on one place: libpetri rejects them at build (CORE-030), so lint never sees them', () => {
    const [A, B] = ['A', 'B'].map(P) as Place<any>[];
    expect(() => Transition.builder('t').inputs(one(A!), one(A!)).outputs(outPlace(B!)).build()).toThrow(/CORE-030/);
  });

  it('flags host arcs into a subnet internal place: reset-across-subnet and encapsulation', () => {
    const [SRC, INBOX, DONE, KILL] = ['SOURCE', 'INBOX', 'DONE', 'KILL'].map(P) as Place<any>[];
    const n = PetriNet.builder('host')
      .transition(tr('arrive', { in: [SRC!], out: [INBOX!] }))
      .transition(tr('kill', { in: [KILL!], reset: [P('s1/busy')] }))
      .transition(tr('peek', { in: [KILL!], read: [P('s1/busy')] }))
      .compose(stageDef().instantiate('s1'), { in: INBOX!, out: DONE! })
      .build();
    const f = lint(n, new Map([['SOURCE', 1], ['KILL', 1]]), bare);
    expect(f).toContainEqual(expect.objectContaining({ rule: 'reset-across-subnet', severity: 'warning', transition: 'kill', place: 's1/busy' }));
    expect(f).toContainEqual(expect.objectContaining({ rule: 'encapsulation', severity: 'warning', transition: 'peek', place: 's1/busy' }));
    expect(f.filter(x => x.transition?.startsWith('s1/'))).toEqual([]);
  });

  it('resolves nested instances with net.subnetOf: an outer transition reading the inner instance is flagged', () => {
    const n = net('nested',
      tr('o1/peek', { in: [P('o1/A')], out: [P('o1/B')], read: [P('o1/inner/X')] }),
      tr('o1/inner/t', { in: [P('o1/inner/X')], out: [P('o1/inner/Y')] }),
    );
    expect(lint(n, new Map([['o1/A', 1], ['o1/inner/X', 1]]), bare)).toContainEqual(
      expect.objectContaining({ rule: 'encapsulation', transition: 'o1/peek', place: 'o1/inner/X' }));
  });

  it('flags ν-join key places fed through undeclared relays; declarations clear it', () => {
    const [REQ, A_MID, B_MID, A_KEY, B_KEY, OUT] = ['REQ', 'A_MID', 'B_MID', 'A_KEY', 'B_KEY', 'OUT'].map(P) as Place<any>[];
    const join = () => tr('join', { in: [A_KEY!, B_KEY!], out: [OUT!] },
      b => b.match(matchSpec(matchKey(A_KEY!, () => nameId('id')), matchKey(B_KEY!, () => nameId('id')))));
    const relayed = net('relayed',
      tr('fork', { in: [REQ!], out: [A_MID!, B_MID!] }),
      tr('workA', { in: [A_MID!], out: [A_KEY!] }),
      tr('workB', { in: [B_MID!], out: [B_KEY!] }),
      join());
    const nuLint = (n: PetriNet, nu?: Candidate['nu']) =>
      lint(n, new Map([['REQ', 1]]), bare, nu).filter(x => x.rule === 'nu-undeclared-carrier');
    const relays = nuLint(relayed, { budgets: ['REQ'] });
    expect(relays.map(x => x.transition).sort()).toEqual(['workA', 'workB']);
    expect(relays.every(x => x.severity === 'error')).toBe(true);
    expect(nuLint(relayed, { budgets: ['REQ'], carriers: ['A_MID', 'B_MID'] })).toEqual([]);

    // A direct co-mint from a pure source is a declared mint once it consumes a declared budget or is
    // listed in nu.mints. Undeclared, libpetri does not read it as a mint (NU-010), so it is flagged
    // along with the missing budget.
    const direct = net('direct', tr('fork', { in: [REQ!], out: [A_KEY!, B_KEY!] }), join());
    expect(nuLint(direct, { budgets: ['REQ'] })).toEqual([]);
    const undeclared = nuLint(direct);
    expect(undeclared).toEqual([
      expect.objectContaining({ severity: 'error', transition: 'join', message: expect.stringMatching(/budget/) }),
      expect.objectContaining({ severity: 'error', transition: 'fork', message: expect.stringMatching(/not a declared mint.*Candidate\.nu\.mints/) }),
    ]);
    expect(undeclared[1]!.message).not.toMatch(/will read .* as a fresh mint/);
    const minted = nuLint(direct, { budgets: [], mints: ['fork'] });
    expect(minted).toEqual([expect.objectContaining({ transition: 'join', message: expect.stringMatching(/budget/) })]);
  });
});

// ─── PNID regressions (research/net-metrics/validation/pnid: nets.ts, RESULTS.md) ─────────────

/** ν fixture builder, as in validation/pnid/src/nets.ts: inputs one each, ν key = the token itself. */
function pnidNet(name: string, spec: Array<[string, string[], string[], string[]?]>): PetriNet {
  const ps = new Map<string, Place<any>>();
  const p = (n: string) => { let x = ps.get(n); if (!x) { x = P(n); ps.set(n, x); } return x; };
  return net(name, ...spec.map(([t, ins, outs, match]) => tr(t, { in: ins.map(p), out: outs.map(p) },
    match ? b => b.match(matchSpec(...match.map(m => matchKey(p(m), (v: unknown) => nameId(String(v)))))) : undefined)));
}
/** P Fig. 13(b): resource closure of 13(a); the second token carrying o stays stuck forever. */
const fig13b = (nu?: Candidate['nu']): Candidate => ({
  name: 'P-Fig13b', rationale: 'fixture', ...(nu ? { nu } : {}),
  build: k => ({
    net: pnidNet('P-Fig13b', [
      ['a', ['R'], ['P1', 'OR']],
      ['b', ['P1'], ['B1', 'B2']],
      ['c', ['B1', 'OR'], ['R'], ['B1', 'OR']],
      ['d', ['B2', 'OR'], ['R'], ['B2', 'OR']],
    ]),
    marking: new Map([['R', k]]),
  }),
});
const fig13bContract: Contract = {
  name: '13b', intent: 'PNID Fig. 13(b)', sinks: ['R'], sources: ['R'],
  properties: [prop('stranded(B2≤2)', { kind: 'placeBound', place: 'B2', bound: 2 })],
};
/** P Fig. 12(b): resource closure 1 of the sound Fig. 12(a). */
const fig12b = (nu?: Candidate['nu']): Candidate => ({
  name: 'P-Fig12b', rationale: 'fixture', ...(nu ? { nu } : {}),
  build: k => ({
    net: pnidNet('P-Fig12b', [
      ['a', ['R'], ['P1', 'OR']],
      ['b', ['P1'], ['B1', 'B2']],
      ['c', ['B1', 'OR'], ['C1', 'OR'], ['B1', 'OR']],
      ['d', ['B2', 'OR'], ['D1', 'OR'], ['B2', 'OR']],
      ['e', ['C1', 'D1'], ['P5'], ['C1', 'D1']],
      ['f', ['P5', 'OR'], ['R'], ['P5', 'OR']],
      ['g', ['P5', 'OR'], [], ['P5', 'OR']],
    ]),
    marking: new Map([['R', k]]),
  }),
});
const fig12bContract: Contract = {
  name: '12b', intent: 'PNID Fig. 12(b)', sinks: ['R'], sources: ['R'],
  properties: [prop('boundOR', { kind: 'placeBound', place: 'OR', bound: 2 })],
};

describe('PNID ν regressions', () => {
  const nuErrors = (r: GateReport) => r.lint.filter(f => f.rule === 'nu-undeclared-carrier' && f.severity === 'error');

  it('13(b) without ν config: the lint fires (budget and relays a, b) and the candidate fails', async () => {
    const r = await runGates(fig13bContract, fig13b());
    expect(nuErrors(r).map(f => f.transition).sort()).toEqual(['a', 'b', 'c']); // c: first join, carries the budget error
    expect(nuErrors(r).some(f => /budget/.test(f.message))).toBe(true);
    expect(r.passed).toBe(false);
  });

  itZ3('13(b) with budget R and carrier P1: the stranding bound is violated at k = 1, 2 (RESULTS.md)', async () => {
    const r = await runGates(fig13bContract, fig13b({ budgets: ['R'], carriers: ['P1'] }));
    expect(nuErrors(r)).toEqual([]);
    for (const k of [1, 2]) {
      const res = result(r, k, 'stranded(B2≤2)');
      expect(res.verdict, `k=${k}: ${res.route} ${res.note}`).toBe('violated');
      expect(res.trace?.filter(t => t === 'b').length).toBeGreaterThanOrEqual(3);
    }
    expect(r.passed).toBe(false);
  });

  it('12(b) without ν config: the lint fires on relays a and b', async () => {
    const r = await runGates(fig12bContract, fig12b());
    expect(nuErrors(r).filter(f => f.place !== undefined).map(f => f.transition).sort()).toEqual(['a', 'b']);
    expect(r.passed).toBe(false);
  });

  itZ3('12(b) with budget R and carriers: lint clean, boundOR proven at k = 1, 2 (RESULTS.md)', async () => {
    const r = await runGates(fig12bContract, fig12b({ budgets: ['R'], carriers: ['P1', 'B1', 'B2', 'C1', 'D1'] }));
    expect(nuErrors(r)).toEqual([]);
    for (const k of [1, 2]) {
      const res = result(r, k, 'boundOR');
      expect(res.verdict, `k=${k}: ${res.route} ${res.note}`).toBe('proven');
    }
  });

  const nuForkDef = () => {
    const i = P('in'), a = P('A'), b = P('B'), o = P('out');
    return SubnetDef.builder('NuFork')
      .place(i).place(a).place(b).place(o)
      .transition(tr('fork', { in: [i], out: [a, b] }))
      .transition(tr('join', { in: [a, b], out: [o] },
        t => t.match(matchSpec(matchKey(a, (v: unknown) => nameId(String(v))), matchKey(b, (v: unknown) => nameId(String(v)))))))
      .inputPort('in', i).outputPort('out', o)
      .build();
  };
  const nuSubnetCandidate = (nu?: Candidate['nu']): Candidate => ({
    name: 'nuSubnet', rationale: 'fixture',
    build: k => ({ net: net('host', tr('arrive', { in: [P('SOURCE')], out: [P('DONE')] })), marking: new Map([['SOURCE', k]]) }),
    subnets: [{ def: nuForkDef(), inputs: ['in'], properties: [prop('nu deadlock-free', { kind: 'deadlockFree' })], ...(nu ? { nu } : {}) }],
  });
  const nuContract: Contract = { name: 'nu', intent: '', sinks: ['DONE'], sources: ['SOURCE'], properties: [] };

  it('refuses to verify a ν SubnetDef without SubnetCheck.nu: unknown, not passed', async () => {
    const r = await runGates(nuContract, nuSubnetCandidate());
    expect(r.compositional[0]!.results).toEqual([expect.objectContaining({
      property: 'nu deadlock-free', verdict: 'unknown', route: 'compositional', note: expect.stringMatching(/^ν subnet without SubnetCheck.nu/),
    })]);
    expect(r.passed).toBe(false);
  });

  // Under bounded(k) the input port is topped up forever, so fork mints without end and the
  // name-aware graph cannot close: libpetri answers unknown whatever the ν configuration. The gate
  // therefore verifies a ν subnet under arrivals(≤k), where k inputs mint at most k names.
  itZ3('verifies a ν SubnetDef with SubnetCheck.nu through SubnetDef.verify(configure), under arrivals(≤k)', async () => {
    for (const nu of [{ budgets: ['in'] }, { budgets: [], mints: ['fork'] }]) {
      const r = await runGates(nuContract, nuSubnetCandidate(nu));
      const res = r.compositional[0]!.results;
      expect(res.map(x => x.property)).toEqual(['nu deadlock-free @arrivals(≤1)', 'nu deadlock-free @arrivals(≤2)']);
      for (const x of res) {
        expect(x, `${JSON.stringify(nu)}: ${x.note}`).toMatchObject({ verdict: 'proven', route: 'nu-scg' });
        expect(x.note).toMatch(/arrivals\(≤k\) instead of bounded\(k\): a ν subnet/);
      }
    }
  });

  itZ3('a ν SubnetCheck.nu that declares no mint leaves the subnet off the ν routes: unknown', async () => {
    const r = await runGates(nuContract, nuSubnetCandidate({ budgets: [] }));
    for (const x of r.compositional[0]!.results) expect(x.verdict, `${x.property}: ${x.note}`).toBe('unknown');
    expect(r.passed).toBe(false);
  });

  it('a ν SubnetCheck.nu naming a missing mint transition is a contract error', async () => {
    const r = await runGates(nuContract, nuSubnetCandidate({ budgets: [], mints: ['forked'] }));
    for (const x of r.compositional[0]!.results) {
      expect(x).toMatchObject({ verdict: 'unknown', route: 'contract' });
      expect(x.note).toMatch(/mint transitions not in 'NuFork': forked/);
    }
  });

  itZ3('Candidate.nu.mints reaches the verifier: a pure-source co-mint is decided on the ν route only when declared', async () => {
    // fork mints one call id per request and stamps it on both branches; join fires per id.
    const fanOut = (nu?: Candidate['nu']): Candidate => ({
      name: 'fan-out', rationale: 'fixture', ...(nu ? { nu } : {}),
      build: k => {
        const [REQ, A, B, OUT] = ['REQ', 'A', 'B', 'OUT'].map(P) as Place<any>[];
        return {
          net: net('fan-out',
            tr('fork', { in: [REQ!], out: [A!, B!] }),
            tr('join', { in: [A!, B!], out: [OUT!] },
              b => b.match(matchSpec(matchKey(A!, (v: unknown) => nameId(String(v))), matchKey(B!, (v: unknown) => nameId(String(v))))))),
          marking: new Map([['REQ', k]]),
        };
      },
    });
    const c: Contract = { name: 'fan-out', intent: '', sinks: ['OUT'], sources: ['REQ'], properties: [prop('no stranded token', { kind: 'deadlockFree' })] };
    const declared = await runGates(c, fanOut({ budgets: [], mints: ['fork'] }));
    for (const k of [1, 2]) expect(result(declared, k, 'no stranded token')).toMatchObject({ verdict: 'proven', route: 'nu-scg' });
    const undeclared = await runGates(c, fanOut({ budgets: [] }));
    for (const k of [1, 2]) expect(result(undeclared, k, 'no stranded token').verdict).toBe('unknown');
    const missing = await runGates(c, fanOut({ budgets: [], mints: ['frok'] }));
    expect(result(missing, 1, 'no stranded token')).toMatchObject({ verdict: 'unknown', route: 'contract' });
  });

  it('a ν config naming a missing place is a contract error', async () => {
    const r = await runGates(fig13bContract, fig13b({ budgets: ['R'], carriers: ['P0'] }));
    const res = result(r, 1, 'stranded(B2≤2)');
    expect(res).toMatchObject({ verdict: 'unknown', route: 'contract' });
    expect(res.note).toMatch(/P0/);
  });
});

describe('compositional gate (z3)', () => {
  const composed = (subnets: Candidate['subnets']) => candidate('staged', k => {
    const [SRC, INBOX, DONE] = ['SOURCE', 'INBOX', 'DONE'].map(P) as Place<any>[];
    const n = PetriNet.builder('staged')
      .transition(tr('arrive', { in: [SRC!], out: [INBOX!] }))
      .compose(stageDef().instantiate('s1'), { in: INBOX!, out: DONE! })
      .build();
    return { net: n, marking: new Map([['SOURCE', k]]) };
  }, subnets);
  const contract: Contract = {
    name: 'staged', intent: 'every event through the stage', sinks: ['DONE'], sources: ['SOURCE'],
    properties: [prop('no stranded token', { kind: 'deadlockFree' }), prop('accounting', { kind: 'accounting', outcomes: ['DONE'] })],
  };

  itZ3('proves each SubnetDef under bounded(1) and bounded(2)', async () => {
    const r = await runGates(contract, composed([{
      def: stageDef(), inputs: ['in'],
      properties: [
        prop('stage deadlock-free', { kind: 'deadlockFree' }),
        prop('port backlog ≤ 2', { kind: 'placeBound', place: 'in', bound: 2 }),
        prop('stage accounting', { kind: 'accounting', outcomes: ['out'] }),
      ],
    }]));
    expect(r.compositional).toHaveLength(1);
    const res = r.compositional[0]!.results;
    expect(res.map(x => x.property)).toEqual([
      'stage deadlock-free @bounded(1)', 'stage deadlock-free @bounded(2)',
      'port backlog ≤ 2 @bounded(1)', 'port backlog ≤ 2 @bounded(2)',
      'stage accounting @arrivals(1..1)', 'stage accounting @arrivals(2..2)',
    ]);
    for (const x of res) expect(x.verdict, `${x.property}: ${x.note}`).toBe('proven');
    for (const x of res.slice(4)) expect(x.note ?? '').not.toMatch(/upper bound only/);
    expect(r.passed).toBe(true);
  });

  itZ3('subnet accounting under arrivals(k) catches a duplicated outcome (vacuous under bounded(k))', async () => {
    const i = P('in'), o = P('out'), d = P('dup');
    const dupDef = SubnetDef.builder('Dup').place(i).place(o).place(d)
      .transition(tr('emit', { in: [i], out: [o, d] }))
      .inputPort('in', i).outputPort('out', o).outputPort('dup', d)
      .build();
    const r = await runGates(contract, composed([{
      def: dupDef, inputs: ['in'], properties: [prop('one outcome per input', { kind: 'accounting', outcomes: ['out', 'dup'] })],
    }]));
    for (const x of r.compositional[0]!.results) {
      expect(x.verdict, x.property).toBe('violated');
      expect(x.trace).toContain('sut/emit');
    }
  });

  itZ3('exact subnet accounting catches a lost input (the upper bound alone would pass it)', async () => {
    // A stage that silently drops an input: fewer outcomes than inputs. Under arrivals(k, k) every
    // input must arrive, so the missing outcome is a violation; an upper-bound check passes it.
    const i = P('in'), o = P('out'), b = P('busy');
    const lossy = SubnetDef.builder('Lossy').place(i).place(o).place(b)
      .transition(tr('start', { in: [i], out: [b] }))
      .transition(tr('finish', { in: [b], out: [o] }))
      .transition(tr('drop', { in: [b] }))
      .inputPort('in', i).outputPort('out', o)
      .build();
    const r = await runGates(contract, composed([{
      def: lossy, inputs: ['in'], properties: [prop('none lost', { kind: 'accounting', outcomes: ['out'] })],
    }]));
    for (const x of r.compositional[0]!.results) {
      expect(x.property).toMatch(/arrivals\(\d\.\.\d\)/);
      expect(x.verdict, x.property).toBe('violated');
      expect(x.trace).toContain('sut/drop');
    }
  });

  itZ3('a subnet that writes an in-out port is verified under arrivals(≤k), since bounded(k) cannot hold', async () => {
    // take borrows a permit from the in-out port, done returns it: a deposit into an environment
    // place, which breaks the Bounded(k) premise (VER-006 AC3), so bounded(k) answers unknown.
    const i = P('in'), permit = P('permit'), busy = P('busy'), o = P('out');
    const borrowDef = SubnetDef.builder('Borrow').place(i).place(permit).place(busy).place(o)
      .transition(tr('take', { in: [i, permit], out: [busy] }))
      .transition(tr('done', { in: [busy], out: [o, permit] }))
      .inputPort('in', i).inoutPort('permit', permit).outputPort('out', o)
      .build();
    const r = await runGates(contract, composed([{
      def: borrowDef, inputs: ['in', 'permit'], properties: [prop('busy ≤ 2', { kind: 'placeBound', place: 'busy', bound: 2 })],
    }]));
    const res = r.compositional[0]!.results;
    expect(res.map(x => x.property)).toEqual(['busy ≤ 2 @arrivals(≤1)', 'busy ≤ 2 @arrivals(≤2)']);
    for (const x of res) {
      expect(x.verdict, `${x.property}: ${x.note}`).toBe('proven');
      expect(x.note).toMatch(/writes in-out port 'permit'/);
    }
  });

  itZ3('finds a violated subnet bound with a trace', async () => {
    // bounded(k) caps the port's occupancy, not the number of injections: busy is unbounded.
    const r = await runGates(contract, composed([{
      def: stageDef(), inputs: ['in'], properties: [prop('stage busy ≤ 1', { kind: 'placeBound', place: 'busy', bound: 1 })],
    }]));
    for (const b of r.compositional[0]!.results) {
      expect(b.verdict).toBe('violated');
      expect(b.trace).toContain('sut/start');
    }
    expect(r.passed).toBe(false);
  });
});

describe('budget', () => {
  it('stops with unknown / "harness budget exhausted" once the total budget is spent', async () => {
    const t0 = performance.now();
    const r = await runGates(workerContract, worker(), { budgetMs: 0 });
    expect(performance.now() - t0).toBeLessThan(500);
    const all = r.smallScope.flatMap(s => s.results);
    expect(all).toHaveLength(10);
    for (const x of all) expect(x).toMatchObject({ verdict: 'unknown', note: 'harness budget exhausted' });
    expect(r.passed).toBe(false);
  });

  itZ3('keeps a run of SMT queries within the total budget (timed net, no enumeration)', async () => {
    // Timed transitions keep every query off the enumeration route, so each spawns z3.
    const c = candidate('timedChain', k => {
      const ts: Transition[] = [];
      const S = P('SOURCE');
      let prev: Place<any> = P('Q0');
      ts.push(tr('arrive', { in: [S], out: [prev] }));
      for (let i = 1; i <= 30; i++) {
        const next = P(`Q${i}`);
        ts.push(tr(`step${i}`, { in: [prev], out: [next] }, b => b.timing(window(1, 2))));
        prev = next;
      }
      return { net: net('timedChain', ...ts), marking: new Map([['SOURCE', k]]) };
    });
    // Quiescence properties go through z3 (≈ 70–130 ms each here); 30 of them cannot fit in 400 ms.
    const properties = Array.from({ length: 30 }, (_, i) => i % 2 === 0
      ? prop(`deadlock-free #${i}`, { kind: 'deadlockFree' })
      : prop(`accounting #${i}`, { kind: 'accounting', outcomes: ['Q30'] }));
    const contract: Contract = { name: 'chain', intent: '', sinks: ['Q30'], sources: ['SOURCE'], properties, scales: [2] };
    const budgetMs = 400;
    const t0 = performance.now();
    const r = await runGates(contract, c, { budgetMs });
    const elapsed = performance.now() - t0;
    expect(elapsed).toBeLessThan(budgetMs + 300);
    const res = r.smallScope[0]!.results;
    expect(res).toHaveLength(30);
    expect(res.some(x => x.note === 'harness budget exhausted')).toBe(true);
    expect(r.passed).toBe(false);
  });
});

// ─── units rule (assume-guarantee over identical per-session instances) ──────────────────────

/** k units s1..sk; each takes permit 1, then permit 2, from one pool of capacity 2 (hold-and-wait). */
function holdAndWait(opts: { crossArc?: boolean } = {}): Candidate {
  return candidate('holdAndWait', k => {
    const PERMIT = P('PERMIT');
    const ts: Transition[] = [];
    const marking = new Map<string, number>([['PERMIT', 2]]);
    for (let i = 1; i <= k; i++) {
      const u = (n: string) => P(`s${i}/${n}`);
      const other = P(`s${i === k ? 1 : i + 1}/HOLD2`);
      ts.push(
        tr(`s${i}/take1`, { in: [u('START'), PERMIT], out: [u('HOLD1')], ...(opts.crossArc ? { inhibit: [other] } : {}) }),
        tr(`s${i}/take2`, { in: [u('HOLD1'), PERMIT], out: [u('HOLD2')] }),
        tr(`s${i}/work`, { in: [u('HOLD2')], out: [u('RELEASING'), PERMIT] }),
        tr(`s${i}/release`, { in: [u('RELEASING')], out: [u('DONE'), PERMIT] }),
      );
      marking.set(`s${i}/START`, 1);
    }
    return { net: net('holdAndWait', ...ts), marking };
  });
}
const holdContract: Contract = {
  name: 'hold', intent: 'every unit finishes', sinks: ['*/DONE', 'PERMIT'], sources: ['*/START'],
  properties: [prop('no stranded token', { kind: 'deadlockFree' }), prop('every unit done', { kind: 'accounting', outcomes: ['*/DONE'] })],
};

/**
 * k units; each takes the one PERMIT and returns it when done, or gives up into STUCK, which nothing
 * consumes, when the permit is gone. At k = 1 the permit is always there; at k = 2 the loser strands.
 */
function contended(): Candidate {
  return candidate('contended', k => {
    const PERMIT = P('PERMIT');
    const ts: Transition[] = [];
    const marking = new Map<string, number>([['PERMIT', 1]]);
    for (let i = 1; i <= k; i++) {
      const u = (n: string) => P(`s${i}/${n}`);
      ts.push(
        tr(`s${i}/take`, { in: [u('START'), PERMIT], out: [u('HOLD')] }),
        tr(`s${i}/work`, { in: [u('HOLD')], out: [u('DONE'), PERMIT] }),
        tr(`s${i}/giveUp`, { in: [u('START')], inhibit: [PERMIT], out: [u('STUCK')] }),
      );
      marking.set(`s${i}/START`, 1);
    }
    return { net: net('contended', ...ts), marking };
  });
}
const contendedContract: Contract = {
  name: 'contended', intent: 'every unit finishes', sinks: ['*/DONE', 'PERMIT'], sources: ['*/START'],
  properties: [prop('no stranded token', { kind: 'deadlockFree' }), prop('every unit done', { kind: 'accounting', outcomes: ['*/DONE'] })],
};

describe('budget via libpetri totalBudget / signal (VER-013)', () => {
  itZ3('stops a long whole-net query at the harness deadline, not at the last-resort race', async () => {
    // Voice step 5 at k = 2 with session S2 starting with one answer already delivered (a sink, so
    // the design stays correct): P1 fails (the instances differ), so the whole-net product runs and
    // does not close within 1.5 s. A second S2/IDLE token also breaks P1, but it lets S2 run two
    // turns at once, which z3 refutes within the budget and so never reaches the deadline.
    const asym: Candidate = {
      ...voiceStep5Minimal,
      build: k => { const b = voiceStep5Minimal.build(k); const m = new Map(b.marking); m.set('S2/ANSWERED', 1); return { net: b.net, marking: m }; },
    };
    const contract: Contract = { ...voiceStep5Contract, scales: [2], properties: [voiceStep5Contract.properties[0]!] };
    const budgetMs = 1_500;
    const t0 = performance.now();
    const r = await runGates(contract, asym, { budgetMs });
    const elapsed = performance.now() - t0;
    const res = r.smallScope[0]!.results[0]!;
    expect(res).toMatchObject({ verdict: 'unknown', route: 'budget' });
    expect(res.note).toMatch(/harness budget exhausted/);
    expect(elapsed).toBeLessThan(budgetMs + 500); // the race alone would return at budget + 1 000 ms
  }, 20_000);
});

describe('units rule', () => {
  it('is off by default (unsound per adversarial review): runGates never reports the units route', async () => {
    const r = await runGates(voiceStep5Contract, voiceStep5Minimal, { budgetMs: 3_000 });
    for (const s of r.smallScope) for (const x of s.results) expect(x.route).not.toBe(UNITS_ROUTE);
  }, 30_000);

  itZ3('proves the voice step-5 design (voice-B1 step5-minimal) at k = 2 by assume-guarantee, well under budget', async () => {
    const t0 = performance.now();
    const r = await runGates(voiceStep5Contract, voiceStep5Minimal, { budgetMs: 30_000, experimentalUnits: true });
    const elapsed = performance.now() - t0;
    const k2 = r.smallScope.find(s => s.k === 2)!.results;
    expect(k2.map(x => x.property)).toEqual(voiceStep5Contract.properties.map(p => p.name));
    for (const x of k2) expect(x).toMatchObject({ verdict: 'proven', route: UNITS_ROUTE });
    expect(k2[0]!.note).toMatch(/P1 2 identical instances.*P3 shared places conserved.*IDLE_SEARCH/);
    for (const x of r.smallScope.find(s => s.k === 1)!.results) expect(x.verdict, x.property).toBe('proven');
    expect(r.passed).toBe(true);
    expect(elapsed).toBeLessThan(10_000);
  }, 40_000);

  it('two-permit hold-and-wait: (a) proves, (b) fails, and the whole-net k = 2 check deadlocks', async () => {
    const u = await checkUnits(holdContract, holdAndWait(), 2);
    expect(u.applicable).toBe(true);
    for (const x of u.a) expect(x.verdict, x.property).toBe('proven');
    expect(u.b).toHaveLength(1);
    expect(u.b[0]!.verdict).toBe('violated');
    expect(u.b[0]!.trace).toContain('steal_PERMIT');
    expect(u.proven).toBe(false);

    const r = await runGates(holdContract, holdAndWait(), { experimentalUnits: true });
    const dl = result(r, 2, 'no stranded token');
    expect(dl.verdict).toBe('violated');
    expect(dl.route).toBe('enumeration');
    expect(dl.trace?.filter(t => t.endsWith('/take1'))).toHaveLength(2);
    expect(dl.note).toMatch(/units rule premises held but not every check proved: \(b\) no hold-and-wait violated/);
    expect(r.passed).toBe(false);
  });

  it('the adversary gadget gives the in-flight split nothing to split (VER-004)', () => {
    // An inhibitor on STOLEN_<R> made the verifier split steal, and adversary_stop could then fire
    // while a steal was in flight, stranding the permit where return could not reach it.
    const built = holdAndWait().build(2);
    const st = analyseUnits(bindStructureOnly(built.net), built.marking);
    if (!st.ok) throw new Error(st.reason);
    for (const withReturn of [true, false]) {
      const iso = st.isolation(withReturn);
      const adversary = [...iso.net.transitions].map(t => t.name).filter(n => /^(steal_|return_|adversary_stop)/.test(n));
      expect(adversary.length).toBeGreaterThan(0);
      expect(inFlightTransitions(iso.net).filter(n => adversary.includes(n)), `withReturn=${withReturn}`).toEqual([]);
      for (const t of iso.net.transitions) if (adversary.includes(t.name)) expect(t.inhibitors, t.name).toEqual([]);
    }
    expect(st.isolation(true).marking.get('UNSTOLEN_PERMIT')).toBe(2);
  });

  it('falls back to the whole net and names P2 when an instance has an arc into another', async () => {
    const u = await checkUnits(holdContract, holdAndWait({ crossArc: true }), 2);
    expect(u).toMatchObject({ applicable: false, premise: 'P2' });
    expect(u.reason).toMatch(/s1\/take1.*s2\/HOLD2/);
    const r = await runGates(holdContract, holdAndWait({ crossArc: true }), { experimentalUnits: true });
    for (const x of r.smallScope.find(s => s.k === 2)!.results) {
      expect(x.route).not.toBe(UNITS_ROUTE);
      expect(x.note).toMatch(/units rule not applicable \(P2 failed\)/);
    }
  });

  it('a local stall under contention is not hidden by the steal/return adversary livelock', async () => {
    // (a) in isolation: the adversary steals the permit, s1 gives up into STUCK. Steal and return
    // stay enabled forever, so without a way for the adversary to stop no marking is quiescent and
    // every quiescence property holds vacuously. The whole net at k = 2 strands the loser.
    const u = await checkUnits(contendedContract, contended(), 2);
    expect(u.applicable).toBe(true);
    const a = u.a.find(x => x.property === 'no stranded token')!;
    expect(a.verdict).toBe('violated');
    expect(a.trace).toContain('s1/giveUp');
    expect(u.proven).toBe(false);

    const r = await runGates(contendedContract, contended(), { experimentalUnits: true });
    for (const x of r.smallScope.find(s => s.k === 1)!.results) expect(x.verdict, x.property).toBe('proven');
    for (const property of ['no stranded token', 'every unit done']) {
      const x = result(r, 2, property);
      expect(x.verdict, property).toBe('violated');
      expect(x.route, property).not.toBe(UNITS_ROUTE);
    }
    expect(r.passed).toBe(false);
  });
});
