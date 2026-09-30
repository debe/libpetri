import { describe, expect, it, vi } from 'vitest';
import type { Candidate, CandidateReport, DesignReport, GateReport, SensorProfile } from '../src/types.js';

const passing: GateReport = {
  lint: [],
  smallScope: [{ k: 1, results: [{ property: 'noStrandedWork', verdict: 'proven', route: 'enumeration', ms: 3 }] }],
  compositional: [{ subnet: 'Guard', results: [{ property: 'alwaysReachesVerdict @bounded(1)', verdict: 'proven', route: 'smt', ms: 80 }] }],
  passed: true,
};
const failing: GateReport = {
  lint: [{ rule: 'dead-power-arc', severity: 'error', transition: 'kill', place: 'answer/IN', message: 'reset on a place nothing touches' }],
  smallScope: [{ k: 1, results: [
    { property: 'noStrandedWork', verdict: 'violated', route: 'enumeration', ms: 1, trace: ['arrive', 'fork', 'kill', 'answer/finish'] },
    { property: 'oneTurnAtATime', verdict: 'unknown', route: 'smt', ms: 900, note: 'budget exhausted' },
  ] }],
  compositional: [],
  passed: false,
};
const sensors = (encap: number): SensorProfile => ({
  size: { places: 13, transitions: 9, arcs: 29 },
  resets: { count: 2, blast: 2, reach: 3, multiToken: 1, crossSubnet: encap },
  encapsulationViolations: encap,
  essentialPowerArcs: 0,
  boundedFraction: 1,
  undeclaredSymmetry: 0,
  routes: { ordinary: false, enumerable: true, nu: false, timed: false },
  stateGrowth: { k1: 19, k2: 100, multiplier: 5.3 },
  timedWidth: 0,
});

vi.mock('../src/gates.js', () => ({
  runGates: vi.fn(async (_c: unknown, cand: Candidate) => (cand.name === 'gate' ? passing : failing)),
}));
vi.mock('../src/sensors.js', () => ({
  measure: vi.fn(async (_c: unknown, cand: Candidate) => sensors(cand.name === 'gate' ? 0 : 2)),
}));

const { runGates } = await import('../src/gates.js');
const { measure } = await import('../src/sensors.js');
const { renderDesignPage } = await import('../src/artifact.js');
const { candidateDot } = await import('../src/dot.js');
const contract = (await import('../examples/guard/contract.js')).default;
const gate = (await import('../examples/guard/gate.js')).default;
const hub = (await import('../examples/guard/hub.js')).default;

async function report(iteration: number, cands: Candidate[]): Promise<DesignReport> {
  const candidates: CandidateReport[] = [];
  for (const c of cands) {
    candidates.push({
      candidate: c.name, rationale: c.rationale, dot: candidateDot(c.build(1).net),
      gates: await runGates(contract, c), sensors: await measure(contract, c),
    });
  }
  return { contract, generatedAt: '2026-09-26T10:00:00Z', iteration, candidates, passing: candidates.filter(c => c.gates.passed).map(c => c.candidate) };
}

describe('renderDesignPage', async () => {
  const r2 = await report(2, [gate, hub]);
  const html = renderDesignPage(r2);

  it('shows the contract and every candidate with its rationale and diagram host', () => {
    expect(html).toContain(contract.intent);
    for (const p of contract.properties) expect(html).toContain(p.name);
    for (const c of [gate, hub]) {
      expect(html).toContain(`id="c-${c.name}"`);
      expect(html).toContain(c.rationale.replace(/'/g, '&#39;'));
    }
    expect(html.match(/class="petrinet-diagram-viewer lp-host"/g)).toHaveLength(2);
  });

  it('shows gate verdicts, lint, routes, traces and pass/fail badges', () => {
    for (const v of ['proven', 'violated', 'unknown']) expect(html).toContain(`class="verdict v-${v}"`);
    expect(html).toContain('dead-power-arc');
    expect(html).toContain('<code>answer/finish</code>');
    expect(html).toContain('budget exhausted');
    expect(html).toContain('<span class="badge pass">passed</span>');
    expect(html).toContain('<span class="badge fail">failed</span>');
    expect(html).toContain('noStrandedWork violated at k=1');
  });

  it('groups sensors and marks size as context only', () => {
    for (const g of ['Encapsulation', 'Resets', 'Decidability', 'Routes and cost', 'Folding hint']) expect(html).toContain(`<h4>${g}</h4>`);
    expect(html).toContain('not a quality signal');
    expect(html).toContain('id="compare"');
  });

  it('embeds the viewer once and mounts every candidate from it', () => {
    expect(html.split('globalThis.LibpetriViewer=').length - 1).toBe(1);
    expect(html).toContain('window.LibpetriViewer.mount(dot, host, { chrome: true })');
    const dots = JSON.parse(/<script type="application\/json" id="lp-dots">([^<]*)<\/script>/.exec(html)![1]!) as string[];
    expect(dots).toHaveLength(2);
    expect(dots[0]).toContain('subgraph cluster_guard');
    expect(html.length).toBeLessThan(8_000_000);
  });

  it('has the theme tokens, dark mode in both forms, and a short title', () => {
    expect(html).toMatch(/:root \{[^}]*--bg:/);
    expect(html).toContain('@media (prefers-color-scheme: dark)');
    expect(html).toContain(':root:not([data-theme="light"])');
    expect(html).toContain(':root[data-theme="dark"]');
    expect(html).toMatch(/body \{[^}]*background: var\(--bg\)/);
    const title = /<title>([^<]*)<\/title>/.exec(html)![1]!;
    expect(title.split(' ').length).toBeGreaterThanOrEqual(2);
    expect(title.split(' ').length).toBeLessThanOrEqual(4);
  });

  it('shows the iteration timeline newest first in live mode', async () => {
    const r1 = await report(1, [hub]);
    const live = renderDesignPage(r2, [r1]);
    const i2 = live.indexOf('<strong>Iteration 2</strong>');
    const i1 = live.indexOf('<strong>Iteration 1</strong>');
    expect(i2).toBeGreaterThan(0);
    expect(i1).toBeGreaterThan(i2);
    expect(live).toContain('added gate');
    expect(html).not.toContain('id="timeline"');
  });
});
