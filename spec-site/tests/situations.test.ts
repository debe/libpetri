// @vitest-environment happy-dom
import { describe, expect, it } from 'vitest';
import type {
  CoverageRow,
  Defect,
  LeanBlock,
  NetTransition,
  ReplayResult,
  SiteData,
  Situation,
  SituationEntry,
  SpecBlock,
  TestCoverage,
} from '../src/model.js';
import type { AppContext } from '../src/app/context.js';
import { buildIndex } from '../src/app/indexes.js';
import { R } from '../src/app/router.js';
import {
  evidenceCounts,
  filterRules,
  groupSituations,
  keyShallSentence,
  neighbours,
  parseStep,
  renderSituation,
  renderSituations,
  ruleCountText,
  ruleStats,
  showFilters,
  signedDate,
  situationCard,
  statusStrip,
  stripSentence,
  stripShares,
  whyHere,
} from '../src/app/situations.js';
import { buildSiteData } from '../src/gen/site.js';

// ---------------------------------------------------------------------------------------------
// Fixture: three rules, two Lean blocks, one open defect, three situations in two groups.
// ---------------------------------------------------------------------------------------------

function block(id: string, title: string, shall: string, extra: Partial<SpecBlock> = {}): SpecBlock {
  return {
    id,
    title,
    file: '01-core-model.md',
    line: 10,
    section: 'Arcs',
    priority: 'MUST',
    kind: 'B',
    status: { state: 'active' },
    body: [
      { kind: 'prose', text: 'Some context about the arc.' },
      { kind: 'shall', text: shall },
    ],
    acceptance: ['It works.'],
    notes: [],
    dependsOn: [],
    mentions: [],
    testDerivation: null,
    terms: [],
    ...extra,
  };
}

function leanBlock(id: string, roles: readonly LeanBlock['evidence'][number]['role'][], signed: string | null = null): LeanBlock {
  return {
    id,
    title: id,
    decl: `Libpetri.Spec.${id.replace('-', '_')}`,
    module: `Libpetri.Spec.Req.${id.replace('-', '_')}`,
    kind: 'B',
    sourceRef: 'spec/01-core-model.md',
    source: 'verbatim',
    scope: 'all executors',
    quotes: [],
    reading: [],
    assumes: [],
    statement: 'theorem x : True',
    signoff: signed === null ? { state: 'pending' } : { state: 'signed', date: signed, hash: '104625b4eefcf18b', by: 'person' },
    hash: '104625b4eefcf18b',
    evidence: roles.map((role, i) => ({ theorem: `Libpetri.Spec.${id}_${role}_${i}`, role, module: 'M', doc: null })),
  };
}

const tested: TestCoverage = { state: 'tested', refs: [] };
const untested: TestCoverage = { state: 'untested' };

function coverage(id: string, java: TestCoverage, ts: TestCoverage, rust: TestCoverage, py: TestCoverage): CoverageRow {
  return { id, leanProofs: [], leanRef: false, tests: { java, typescript: ts, rust, python: py } };
}

const take: NetTransition = {
  name: 'take',
  inputs: [{ kind: 'one', place: 'job' }],
  inhibitors: ['lock'],
  reads: [],
  resets: [],
  output: { type: 'place', place: 'lock' },
  priority: 0,
  timing: null,
};
const release: NetTransition = { ...take, name: 'release', inputs: [{ kind: 'one', place: 'lock' }], inhibitors: [], output: { type: 'place', place: 'done' } };

function situation(slug: string, group: Situation['group'], cites: readonly string[], steps: readonly string[], replay = true, blockedLast = false): Situation {
  return {
    slug,
    title: `Title of ${slug}`,
    text: `Text of ${slug}.`,
    group,
    cites,
    replay,
    notReplayed: replay ? null : 'timed',
    net: { places: ['job', 'lock', 'done'], marking: { job: 2 }, transitions: [take, release], properties: [] },
    steps: steps.map((fire, i) => ({ fire, branch: 0, timeout: false, text: null, expect: blockedLast && i === steps.length - 1 ? 'blocked' as const : 'fired' as const })),
  };
}

const blockedResult: ReplayResult = {
  slug: 'gate',
  reference: 'r',
  initial: { job: 2 },
  complete: false,
  steps: [
    { kind: 'fired', index: 0, fire: 'take', branch: 0, timeout: false, marking: { job: 1, lock: 1 } },
    {
      kind: 'blocked',
      index: 1,
      fire: 'take',
      branch: 0,
      timeout: false,
      reason: { kind: 'inhibitorMarked', place: 'lock', count: 1 },
      requirement: 'CORE-031',
      message: "'take' is not enabled: inhibitor place 'lock' holds 1 token",
    },
  ],
};

const fullResult: ReplayResult = {
  slug: 'cycle',
  reference: 'r',
  initial: { job: 2 },
  complete: true,
  steps: [
    { kind: 'fired', index: 0, fire: 'take', branch: 0, timeout: false, marking: { job: 1, lock: 1 } },
    { kind: 'fired', index: 1, fire: 'release', branch: 0, timeout: false, marking: { done: 1, job: 1 } },
  ],
};

const defect: Defect = {
  id: 'RD-07',
  title: 'Inhibitor ignored',
  requirements: ['CORE-031'],
  runtimes: ['python'],
  text: 'x',
  evidence: [],
  evidenceText: 'none',
  fix: null,
  status: { state: 'open' },
};

function fixture(): SiteData {
  return buildSiteData({
    spec: {
      files: [],
      blocks: [
        block('CORE-022', 'Transition enablement', 'A transition is enabled when its inputs hold enough tokens. The executor shall fire only enabled transitions. More text follows.'),
        block('CORE-030', 'Input arc', 'An input arc shall consume tokens.'),
        block('CORE-031', 'Inhibitor arc', 'When the inhibitor place holds a token, the transition shall not be enabled.'),
      ],
    },
    glossary: [],
    lean: {
      blocks: [
        leanBlock('CORE-031', ['holds', 'forbids', 'forbids', 'mutant', 'nonvacuous'], '2026-11-10'),
        leanBlock('CORE-022', ['forbids']),
      ],
      citations: [],
    },
    coverage: {
      'CORE-022': coverage('CORE-022', tested, tested, tested, untested),
      'CORE-030': coverage('CORE-030', untested, tested, tested, untested),
      'CORE-031': coverage('CORE-031', tested, tested, tested, tested),
    },
    defects: [defect],
    situations: [
      { situation: situation('gate', 'Firing', ['CORE-022'], ['take', 'take'], true, true), result: blockedResult },
      { situation: situation('cycle', 'Firing', ['CORE-030'], ['take', 'release']), result: { ...fullResult } },
      { situation: situation('late', 'Time', ['CORE-031'], [], false), result: null },
    ],
    diagrams: new Set(),
  });
}

function context(data: SiteData = fixture()): AppContext {
  const index = buildIndex(data);
  const ctx: AppContext = {
    data,
    index,
    render: () => {
      throw new Error('not used');
    },
    navigate: () => {},
  };
  return ctx;
}

function entry(ctx: AppContext, slug: string): SituationEntry {
  const e = ctx.index.situations.get(slug);
  if (e === undefined) throw new Error(`no situation ${slug}`);
  return e;
}

// ---------------------------------------------------------------------------------------------

describe('grouping and order', () => {
  it('groups in the fixed group order and leaves out empty groups', () => {
    const ctx = context();
    const groups = groupSituations(ctx.data.situations);
    expect(groups.map((g) => g.group)).toEqual(['Firing', 'Time']);
    expect(groups[0]?.entries.map((e) => e.slug)).toEqual(['cycle', 'gate']);
    expect(groups[0]?.intro).toMatch(/fire/);
  });

  it('finds neighbours in home order', () => {
    const { situations } = context().data;
    expect(neighbours(situations, 'cycle').prev).toBeNull();
    expect(neighbours(situations, 'gate').prev?.slug).toBe('cycle');
    expect(neighbours(situations, 'gate').next?.slug).toBe('late');
    expect(neighbours(situations, 'late').next).toBeNull();
    expect(neighbours(situations, 'nope')).toEqual({ prev: null, next: null });
  });

  it('reads ?step= as a clamped integer', () => {
    expect(parseStep({}, 3)).toBe(0);
    expect(parseStep({ step: '2' }, 3)).toBe(2);
    expect(parseStep({ step: '9' }, 3)).toBe(3);
    expect(parseStep({ step: '-1' }, 3)).toBe(0);
    expect(parseStep({ step: '1.5' }, 3)).toBe(0);
    expect(parseStep({ step: 'x' }, 3)).toBe(0);
  });
});

describe('rule counts and the status strip', () => {
  it('counts rules, rules proved in Lean and open defects', () => {
    const ctx = context();
    const gate = entry(ctx, 'gate');
    // CORE-022 cited, CORE-031 from the blocked step.
    expect(gate.rules.map((r) => r.id)).toEqual(['CORE-022', 'CORE-031']);
    const stats = ruleStats(ctx, gate);
    expect(stats.rules).toBe(2);
    expect(stats.proved).toBe(1); // CORE-022's block has no holds theorem
    expect(stats.defects.map((d) => d.id)).toEqual(['RD-07']);
    expect(ruleCountText(stats)).toBe('2 rules · 1 proved in Lean');
    expect(ruleCountText({ rules: 1, proved: 0, defects: [] })).toBe('1 rule · 0 proved in Lean');
  });

  it('builds one column for Lean and one per runtime; a defect overrides tested', () => {
    const ctx = context();
    const cols = statusStrip(ctx, ['CORE-022', 'CORE-031']);
    expect(cols.map((c) => [c.key, c.ok, c.defect, c.total])).toEqual([
      ['lean', 2, 0, 2],
      ['java', 2, 0, 2],
      ['typescript', 2, 0, 2],
      ['rust', 2, 0, 2],
      ['python', 0, 1, 2],
    ]);
    expect(stripSentence(cols)).toBe(
      'Lean block for 2 of 2. Java tested 2 of 2. TypeScript tested 2 of 2. Rust tested 2 of 2. Python tested 0 of 2, 1 open defect.',
    );
    expect(stripShares(cols[4]!)).toEqual({ ok: 0, defect: 50 });
    expect(stripShares({ key: 'lean', label: 'Lean', short: 'Lean', ok: 0, defect: 0, total: 0 })).toEqual({ ok: 0, defect: 0 });
  });
});

describe('rule card derivations', () => {
  it('takes the first shall sentence of the first shall paragraph', () => {
    const ctx = context();
    expect(keyShallSentence(ctx.index.blocks.get('CORE-022')!)).toBe('The executor shall fire only enabled transitions.');
    expect(keyShallSentence(ctx.index.blocks.get('CORE-031')!)).toBe(
      'When the inhibitor place holds a token, the transition shall not be enabled.',
    );
    expect(keyShallSentence(block('X-1', 'x', 'y', { body: [{ kind: 'prose', text: 'No rule here.' }] }))).toBeNull();
  });

  it('counts evidence per role in the reader order', () => {
    const counts = evidenceCounts(context().index.lean('CORE-031'));
    expect(counts).toEqual([
      { role: 'holds', count: 1 },
      { role: 'nonvacuous', count: 1 },
      { role: 'forbids', count: 2 },
      { role: 'mutant', count: 1 },
    ]);
  });

  it('says why a rule is on the page and filters by link kind', () => {
    expect(whyHere([{ kind: 'cited' }, { kind: 'step', index: 3 }, { kind: 'exercised' }])).toEqual([
      'cited by this situation',
      'cited by step 4',
      'the net uses a feature it governs',
    ]);
    const rules = [
      { id: 'A-1', links: [{ kind: 'cited' }] },
      { id: 'A-2', links: [{ kind: 'step', index: 0 }] },
      { id: 'A-3', links: [{ kind: 'exercised' }] },
    ] as const;
    expect(filterRules(rules, 'all')).toHaveLength(3);
    expect(filterRules(rules, 'cited').map((r) => r.id)).toEqual(['A-1', 'A-2']);
    expect(filterRules(rules, 'exercised').map((r) => r.id)).toEqual(['A-3']);
    expect(showFilters(rules)).toBe(true);
    expect(showFilters(rules.slice(0, 2))).toBe(false); // every rule is cited, nothing exercised
  });

  it('picks the newest signoff date', () => {
    expect(signedDate([leanBlock('A-1', []), leanBlock('A-1', [], '2026-11-10'), leanBlock('A-1', [], '2026-10-01')])).toBe('2026-11-10');
    expect(signedDate([leanBlock('A-1', [])])).toBeNull();
  });
});

describe('views', () => {
  it('renders the home page with one h1, groups, stats and cards', () => {
    const ctx = context();
    const view = renderSituations(ctx, R.situations());
    const node = view.node as HTMLElement;
    expect(view.title).toBe('libpetri spec');
    expect(node.querySelectorAll('h1')).toHaveLength(1);
    expect([...node.querySelectorAll('h2')].map((x) => x.textContent)).toEqual(['Firing', 'Time']);
    expect(node.querySelectorAll('.sit-card a.sit-card__link')).toHaveLength(3);
    expect(node.querySelector('.sit-stats')?.textContent).toContain('2 of 3with a Lean block');
    expect([...node.querySelectorAll('.sit-stat')].every((li) => li.querySelector('a') !== null)).toBe(true);
    expect(node.querySelector('.situations__start a')?.getAttribute('href')).toBe('#/situation/cycle');
  });

  it('renders a card with counts, a defect badge, a strip with a text equivalent and the replay line', () => {
    const ctx = context();
    const card = situationCard(ctx, entry(ctx, 'gate'));
    expect(card.querySelector('a')?.getAttribute('href')).toBe('#/situation/gate');
    expect(card.querySelector('a')?.textContent).toBe(card.querySelector('.sit-card__title')?.textContent);
    expect(card.querySelector('.sit-card__count')?.textContent).toBe('2 rules · 1 proved in Lean');
    expect(card.querySelector('.sit-card__defects')?.textContent).toContain('1 open defect');
    expect(card.querySelectorAll('.sit-strip__bar')).toHaveLength(5);
    expect(card.querySelector('.sit-strip .sr-only')?.textContent).toContain('Python tested 0 of 2, 1 open defect.');
    expect(card.querySelector('.sit-card__replay')?.textContent).toBe('▶ Replayed by Lean · 2 steps');
    // One link per card (the title, stretched over the card); nothing else is focusable.
    expect(card.querySelectorAll('a, button')).toHaveLength(1);
    expect(situationCard(ctx, entry(ctx, 'late')).querySelector('.sit-card__replay')?.textContent).toBe('Not replayed (timed)');
  });

  it('renders a situation page with the player, verdict and one rule card per rule', () => {
    const ctx = context();
    const view = renderSituation(ctx, R.situation('gate', 1));
    const node = view.node as HTMLElement;
    try {
      expect(view.title).toBe('Title of gate');
      expect(node.querySelectorAll('h1')).toHaveLength(1);
      expect(node.querySelector('.sit-page__stage')?.childElementCount).toBe(1);
      expect([...node.querySelectorAll('.rule-card')].map((c) => c.getAttribute('data-rule'))).toEqual(['CORE-022', 'CORE-031']);
      const inhibitor = node.querySelector('[data-rule="CORE-031"]');
      expect(inhibitor?.textContent).toContain('Signed 2026-11-10');
      expect(inhibitor?.textContent).toContain('RD-07');
      expect(inhibitor?.querySelector('.rule-card__why')?.textContent).toBe('Why here: cited by step 2 · the net uses a feature it governsOpen rule CORE-031 ›');
      expect(inhibitor?.querySelector('.rule-card__why a')?.getAttribute('href')).toBe('#/req/CORE-031');
      expect(node.querySelector('[data-rule="CORE-022"]')?.textContent).toContain('Not signed');
      expect(node.querySelector('[rel="next"]')?.getAttribute('href')).toBe('#/situation/late');
    } finally {
      view.dispose?.();
    }
  });

  it('filters the rule cards with the chips when a filter splits the list', () => {
    const ctx = context();
    // The gate net has an inhibitor arc, so CORE-031 is also exercised; drop those links to get
    // a list where every rule is cited and no filter splits it.
    const gate = entry(ctx, 'gate');
    const citedOnly: SituationEntry = { ...gate, rules: gate.rules.map((r) => ({ ...r, links: r.links.filter((l) => l.kind !== 'exercised') })) };
    const withGate = (e: SituationEntry): SiteData => ({ ...ctx.data, situations: ctx.data.situations.map((s) => (s.slug === 'gate' ? e : s)) });
    const plain = renderSituation(context(withGate(citedOnly)), R.situation('gate'));
    expect(plain.node.textContent).not.toContain('Exercised');
    plain.dispose?.();
    const mixed: SituationEntry = { ...citedOnly, rules: [...citedOnly.rules, { id: 'CORE-030', links: [{ kind: 'exercised' }] }] };
    const data = withGate(mixed);
    const view = renderSituation(context(data), R.situation('gate'));
    const node = view.node as HTMLElement;
    try {
      const chip = node.querySelector<HTMLButtonElement>('.filter-chip[data-filter="exercised"]');
      chip?.click();
      expect(chip?.getAttribute('aria-pressed')).toBe('true');
      expect([...node.querySelectorAll('.rule-card')].map((c) => c.getAttribute('data-rule'))).toEqual(['CORE-030']);
      expect(node.querySelector('[data-rule="CORE-030"] .rule-card__why > span')?.textContent).toBe('Why here: the net uses a feature it governs');
    } finally {
      view.dispose?.();
    }
  });

  it('renders not found for an unknown slug without throwing', () => {
    const view = renderSituation(context(), R.situation('nope'));
    expect(view.title).toBe('Nothing here');
    expect((view.node as HTMLElement).textContent).toContain('#/situation/nope does not match a page.');
  });

  it('moves between situations with [ and ] and stops listening on dispose', () => {
    const ctx = context();
    const seen: string[] = [];
    const nav: AppContext = { ...ctx, navigate: (route) => { if (route.view === 'situation') seen.push(route.slug); } };
    const view = renderSituation(nav, R.situation('gate'));
    document.dispatchEvent(new KeyboardEvent('keydown', { key: ']' }));
    document.dispatchEvent(new KeyboardEvent('keydown', { key: '[' }));
    view.dispose?.();
    document.dispatchEvent(new KeyboardEvent('keydown', { key: ']' }));
    expect(seen).toEqual(['late', 'cycle']);
  });
});
