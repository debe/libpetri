// @vitest-environment happy-dom
/**
 * The self-test's own tests: it plans a view for every rule, situation step and graph node, its
 * data checks pass on the real data, and planted faults in the data are caught.
 */
import { beforeAll, describe, expect, it } from 'vitest';
import type { AppContext } from '../src/app/context.js';
import { buildIndex } from '../src/app/indexes.js';
import { formatRoute, R, reqGraph } from '../src/app/router.js';
import { graphNodes, runSelftest, sampleRoutes, type SelftestGroup } from '../src/app/selftest.js';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { renderRoute } from '../src/app/views.js';
import { decode } from '../src/decode.js';
import { siteData } from '../src/decode-site.js';
import type { SiteData, SpecBlock } from '../src/model.js';
import { nodeKey, SITE_DATA_ELEMENT_ID } from '../src/model.js';

let data: SiteData;

beforeAll(() => {
  // The generator cannot load under happy-dom (it resolves paths through file: URLs), so build
  // the page in a child process, as `npm run build` does, and read it back.
  const dir = mkdtempSync(join(tmpdir(), 'spec-site-selftest-'));
  try {
    const out = join(dir, 'index.html');
    execFileSync(process.execPath, [join(process.cwd(), 'node_modules', 'tsx', 'dist', 'cli.mjs'), 'src/gen/main.ts', '--out', out, '--no-landing'], { stdio: 'pipe' });
    const parsed = new DOMParser().parseFromString(readFileSync(out, 'utf8'), 'text/html');
    data = decode(siteData, JSON.parse(parsed.getElementById(SITE_DATA_ELEMENT_ID)?.textContent ?? 'null'));
    // Put the page's diagram templates into this document, as the real page has them.
    const diagrams = parsed.getElementById('diagrams');
    if (diagrams !== null) document.body.append(document.importNode(diagrams, true));
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}, 60_000);

function contextFor(d: SiteData): AppContext {
  const index = buildIndex(d);
  const ctx: AppContext = { data: d, index, render: (route) => renderRoute(ctx, route), navigate: () => undefined };
  return ctx;
}

const DATA_ONLY: ReadonlySet<SelftestGroup> = new Set<SelftestGroup>(['Data invariants']);

describe('sampleRoutes', () => {
  it('covers every rule, every situation step, every graph node and every impact', () => {
    const routes = new Set(sampleRoutes(data).map(([, route]) => formatRoute(route)));
    for (const b of data.blocks) {
      expect(routes).toContain(formatRoute(R.req(b.id)));
      expect(routes).toContain(formatRoute(reqGraph(b.id, 'impact')));
    }
    for (const s of data.situations) {
      for (let step = 0; step <= s.steps.length; step++) expect(routes).toContain(formatRoute(R.situation(s.slug, step)));
    }
    for (const node of graphNodes(data)) expect(routes).toContain(formatRoute(R.graph(node)));
    for (const route of [R.situations(), R.req(), R.conf(), R.graph()]) expect(routes).toContain(formatRoute(route));
  });

  it('lists each graph node once', () => {
    const keys = graphNodes(data).map(nodeKey);
    expect(new Set(keys).size).toBe(keys.length);
  });
});

describe('data invariants', () => {
  it('pass on the data the build embeds', () => {
    const report = runSelftest(contextFor(data), DATA_ONLY);
    expect(report.checks.filter((c) => c.error !== null)).toEqual([]);
    expect(report.checks.length).toBeGreaterThan(0);
  });

  it('catch a dangling dependency, a wrong count and an edge to nowhere', () => {
    const planted: SpecBlock = {
      id: 'PLANT-001',
      title: 'Planted',
      file: data.files[0]?.file ?? '01-core-model.md',
      line: 1,
      section: null,
      priority: 'MUST',
      kind: 'B',
      status: { state: 'active' },
      body: [],
      acceptance: [],
      notes: [],
      dependsOn: ['NOPE-404'],
      mentions: [],
      testDerivation: null,
      terms: ['no-such-term'],
    };
    const broken: SiteData = {
      ...data,
      blocks: [...data.blocks, planted],
      edges: [...data.edges, { kind: 'mentions', from: 'PLANT-001', to: 'NOPE-405' }],
    };
    const failures = runSelftest(contextFor(broken), DATA_ONLY).checks.filter((c) => c.error !== null);
    const text = failures.map((f) => `${f.name}: ${f.error ?? ''}`).join('\n');
    expect(text).toContain('PLANT-001: every ID link and glossary term resolves: depends on unknown NOPE-404');
    expect(text).toContain('uses term no-such-term');
    expect(text).toContain(`activeIds says ${data.counts.activeIds}, the data has ${data.counts.activeIds + 1}`);
    expect(text).toContain('mentions edge to unknown NOPE-405');
  });
});
