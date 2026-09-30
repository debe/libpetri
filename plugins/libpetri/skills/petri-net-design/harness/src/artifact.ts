/**
 * Renders the design comparison page: one self-contained HTML file the agent publishes as an
 * artifact and republishes on every iteration of the design loop.
 *
 * The libpetri viewer (DOT → SVG with Graphviz WASM, cluster overlay, legend) is inlined once
 * (~3 MB, the WASM is base64 inside the IIFE); every candidate's DOT is embedded as JSON and mounted
 * from that single copy with `window.LibpetriViewer.mount(dot, host, { chrome: true })`, lazily as
 * each diagram scrolls into view.
 */
import { readFileSync } from 'node:fs';
import { createRequire } from 'node:module';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import type {
  CandidateReport, Contract, DesignReport, GateReport, LintFinding, NamedProperty, PropertyResult,
  PropertySpec, SensorProfile, Verdict,
} from './types.js';

// ───────────────────────────── assets ─────────────────────────────

interface ViewerAssets { readonly js: string; readonly css: string }
let assets: ViewerAssets | null = null;

function viewerAssets(): ViewerAssets {
  if (assets) return assets;
  let js: string;
  let css: string;
  try {
    const req = createRequire(import.meta.url);
    js = readFileSync(req.resolve('libpetri/viewer/iife'), 'utf8');
    css = readFileSync(req.resolve('libpetri/viewer/css'), 'utf8');
  } catch {
    const dir = join(dirname(fileURLToPath(import.meta.url)), '..', 'node_modules', 'libpetri', 'dist', 'viewer');
    js = readFileSync(join(dir, 'viewer.iife.js'), 'utf8');
    css = readFileSync(join(dir, 'viewer.css'), 'utf8');
  }
  // Inline-script safety: a literal "</script" would end the element early.
  assets = { js: js.replace(/<\/script/gi, '<\\/script'), css: css.replace(/<\/style/gi, '<\\/style') };
  return assets;
}

// ───────────────────────────── helpers ─────────────────────────────

const esc = (s: unknown): string =>
  String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;').replace(/'/g, '&#39;');

const slug = (s: string): string => 'c-' + s.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '');

const pct = (x: number): string => (x < 0 ? 'n/a' : `${Math.round(x * 100)}%`);
const num = (x: number, na = 'n/a'): string => (x < 0 ? na : String(x));
const ms = (x: number): string => (x < 1000 ? `${Math.round(x)} ms` : `${(x / 1000).toFixed(1)} s`);

function pageTitle(contract: Contract): string {
  const words = contract.name.trim().split(/\s+/).filter(Boolean);
  return words.length >= 1 && words.length <= 3 ? `${contract.name} designs` : 'Petri net designs';
}

function specText(spec: PropertySpec): string {
  switch (spec.kind) {
    case 'deadlockFree': return 'Every quiescent marking holds tokens only in declared sinks.';
    case 'accounting': return `At quiescence, ${spec.outcomes.join(' + ')} hold exactly the tokens the sources supplied` +
      (spec.perUnit && spec.perUnit !== 1 ? ` (×${spec.perUnit} per unit).` : '.');
    case 'mutualExclusion': return `${spec.a} and ${spec.b} are never marked together.`;
    case 'placeBound': return `${spec.place} never holds more than ${spec.bound} token${spec.bound === 1 ? '' : 's'}.`;
    case 'unreachable': return `No reachable marking marks ${spec.places.join(' and ')}.`;
  }
}

function verdictCounts(g: GateReport): Record<Verdict, number> {
  const c: Record<Verdict, number> = { proven: 0, violated: 0, unknown: 0, skipped: 0 };
  for (const s of g.smallScope) for (const r of s.results) c[r.verdict]++;
  for (const s of g.compositional) for (const r of s.results) c[r.verdict]++;
  return c;
}

const lintCount = (g: GateReport, sev: LintFinding['severity']): number => g.lint.filter(l => l.severity === sev).length;

function badge(passed: boolean): string {
  return passed ? '<span class="badge pass">passed</span>' : '<span class="badge fail">failed</span>';
}

function verdictChip(v: Verdict): string {
  return `<span class="verdict v-${v}">${v}</span>`;
}

/** Why a failing candidate failed, in one line. */
function failureSummary(g: GateReport): string {
  if (g.passed) return 'All gates green.';
  const parts: string[] = [];
  const errs = lintCount(g, 'error');
  if (errs) parts.push(`${errs} lint error${errs === 1 ? '' : 's'}`);
  const seen = new Set<string>();
  for (const s of g.smallScope) for (const r of s.results) {
    if (r.verdict === 'violated' || r.verdict === 'unknown') {
      const key = `${r.property} ${r.verdict}`;
      if (!seen.has(key)) { seen.add(key); parts.push(`${r.property} ${r.verdict} at k=${s.k}`); }
    }
  }
  for (const s of g.compositional) for (const r of s.results) {
    if (r.verdict === 'violated' || r.verdict === 'unknown') parts.push(`${s.subnet}: ${r.property} ${r.verdict}`);
  }
  return parts.length ? parts.join(' · ') : 'Gate reported failure.';
}

// ───────────────────────────── sensors ─────────────────────────────

interface SensorRow {
  readonly label: string;
  readonly value: string;
  readonly meaning: string;
  /** Whether the value deserves the reader's attention (not a score; just a highlight). */
  readonly flag?: boolean;
}

interface SensorGroup { readonly title: string; readonly blurb: string; readonly rows: readonly SensorRow[] }

function sensorGroups(s: SensorProfile): SensorGroup[] {
  return [
    {
      title: 'Encapsulation',
      blurb: 'Whether subnets can be proven on their own.',
      rows: [
        { label: 'Arcs into subnet internals', value: num(s.encapsulationViolations), flag: s.encapsulationViolations > 0,
          meaning: 'Arcs from outside a subnet into a non-port place. Any of them blocks the compositional proof.' },
        { label: 'Resets across a subnet boundary', value: num(s.resets.crossSubnet), flag: s.resets.crossSubnet > 0,
          meaning: 'A host clearing another subnet\'s places by name; breaks silently when composition renames them.' },
      ],
    },
    {
      title: 'Resets',
      blurb: 'Reset arcs discard tokens; these say how much and how blindly.',
      rows: [
        { label: 'Reset arcs', value: num(s.resets.count), meaning: 'Total reset arcs in the net.' },
        { label: 'Blast', value: num(s.resets.blast),
          meaning: 'Most places a single transition resets at once.' },
        { label: 'Reach', value: num(s.resets.reach), meaning: 'Other transitions touching a reset place: how far a reset\'s effect travels.' },
        { label: 'Multi-token resets', value: num(s.resets.multiToken, 'did not close'), flag: s.resets.multiToken !== 0,
          meaning: 'Resets on places that can hold more than one token: they discard other units\' work too.' },
      ],
    },
    {
      title: 'Decidability',
      blurb: 'Whether the verifier can reach a verdict as the net scales.',
      rows: [
        { label: 'Essential power arcs', value: num(s.essentialPowerArcs, 'z3 unavailable'), flag: s.essentialPowerArcs > 0,
          meaning: 'Reset/inhibitor arcs on structurally unbounded places: the Turing-powerful fragment where proofs may return unknown.' },
        { label: 'Bounded places', value: pct(s.boundedFraction), 
          meaning: 'Share of places with a structural bound (invariants plus the self-guarded latch rule: every producer consumes the place).' },
        { label: 'Ordinary net', value: s.routes.ordinary ? 'yes' : 'no',
          meaning: 'No weighted, inhibitor, read or reset arcs: the siphon/trap route applies (only without sinks).' },
      ],
    },
    {
      title: 'Routes and cost',
      blurb: 'Which verification routes apply, and how the state space grows.',
      rows: [
        { label: 'Enumerable', value: s.routes.enumerable ? 'yes' : 'no',
          meaning: 'Untimed, no environment places, no ν: exact state-space enumeration applies.' },
        { label: 'ν-correlated', value: s.routes.nu ? 'yes' : 'no', meaning: 'Uses correlated fork/join by identity; verified on the ν state-class graph.' },
        { label: 'Timed', value: s.routes.timed ? 'yes' : 'no', meaning: 'Has non-immediate timing; timed proofs use the state-class graph.' },
        { label: 'State classes k=1 → k=2', value: `${num(s.stateGrowth.k1)} → ${num(s.stateGrowth.k2)}`,
          meaning: 'Untimed reachable states at scale 1 and 2.' },
        { label: 'Per-unit multiplier', value: s.stateGrowth.multiplier > 0 ? `×${round(s.stateGrowth.multiplier)}` : 'n/a',

          meaning: 'How much the state space multiplies per added unit: the cost of proving at larger k.' },
        { label: 'Timed width', value: num(s.timedWidth),
          meaning: 'Most non-immediate transitions enabled together; drives timed-proof cost.' },
      ],
    },
    {
      title: 'Folding hint',
      blurb: 'Repetition that could be a declared subnet or a coloured token instead.',
      rows: [
        { label: 'Undeclared symmetry', value: pct(s.undeclaredSymmetry), flag: s.undeclaredSymmetry > 0,
          meaning: 'Share of top-level transitions that are exact structural twins. A hint to fold, not a score.' },
      ],
    },
  ];
}

function round(x: number): string {
  return x >= 10 ? x.toFixed(0) : x.toFixed(1).replace(/\.0$/, '');
}

function renderSensors(s: SensorProfile): string {
  const groups = sensorGroups(s).map(g => `
    <section class="sgroup">
      <h4>${esc(g.title)}</h4>
      <p class="muted small">${esc(g.blurb)}</p>
      <dl>${g.rows.map(r => `
        <div class="srow${r.flag ? ' flag' : ''}">
          <dt>${esc(r.label)}</dt><dd class="sval">${esc(r.value)}</dd>
          <dd class="smeaning">${esc(r.meaning)}</dd>
        </div>`).join('')}
      </dl>
    </section>`).join('');
  const size = `
    <section class="sgroup size">
      <h4>Size <span class="tag">context only · not a quality signal</span></h4>
      <p class="muted small">Size metrics ranked human-labelled fixes backwards in the lab; a bigger net is often the better one.</p>
      <p class="sizeline">${s.size.places} places · ${s.size.transitions} transitions · ${s.size.arcs} arcs</p>
    </section>`;
  return `<div class="sgrid">${groups}${size}</div>`;
}

// ───────────────────────────── gates ─────────────────────────────

function renderTrace(trace: readonly string[] | undefined): string {
  if (!trace || trace.length === 0) return '<span class="muted">—</span>';
  const steps = trace.map(t => `<code>${esc(t)}</code>`).join('<span class="arrow">→</span>');
  if (trace.length <= 8) return `<div class="trace">${steps}</div>`;
  return `<details class="trace-d"><summary>${trace.length} firings, ends <code>${esc(trace[trace.length - 1])}</code></summary><div class="trace">${steps}</div></details>`;
}

function resultRows(results: readonly PropertyResult[], lead: string): string {
  return results.map((r, i) => `
    <tr class="r-${r.verdict}">
      ${i === 0 ? `<th scope="row" rowspan="${results.length}">${lead}</th>` : ''}
      <td>${esc(r.property)}</td>
      <td>${verdictChip(r.verdict)}</td>
      <td>${esc(r.route)}</td>
      <td class="num">${ms(r.ms)}</td>
      <td>${renderTrace(r.trace)}${r.note ? `<div class="note">${esc(r.note)}</div>` : ''}</td>
    </tr>`).join('');
}

function renderGates(g: GateReport): string {
  const lint = g.lint.length === 0
    ? '<p class="ok small">No lint findings.</p>'
    : `<ul class="lint">${g.lint.map(l => `
        <li class="sev-${l.severity}"><span class="sev">${l.severity}</span> <code>${esc(l.rule)}</code>
        ${l.transition ? ` on <code>${esc(l.transition)}</code>` : ''}${l.place ? ` → <code>${esc(l.place)}</code>` : ''}
        <div>${esc(l.message)}</div></li>`).join('')}</ul>`;
  const small = g.smallScope.length === 0
    ? '<p class="muted small">No small-scope results.</p>'
    : `<div class="table-wrap"><table class="gt">
        <thead><tr><th>k</th><th>Property</th><th>Verdict</th><th>Route</th><th class="num">Time</th><th>Counterexample</th></tr></thead>
        <tbody>${g.smallScope.map(s => resultRows(s.results, `k=${s.k}`)).join('')}</tbody></table></div>`;
  const comp = g.compositional.length === 0
    ? '<p class="muted small">No subnets declared for isolated verification.</p>'
    : `<div class="table-wrap"><table class="gt">
        <thead><tr><th>Subnet</th><th>Property</th><th>Verdict</th><th>Route</th><th class="num">Time</th><th>Counterexample</th></tr></thead>
        <tbody>${g.compositional.map(s => resultRows(s.results, esc(s.subnet))).join('')}</tbody></table></div>`;
  return `
    <h4>Lint</h4>${lint}
    <h4>Small-scope gate</h4>${small}
    <h4>Compositional gate</h4>${comp}`;
}

// ───────────────────────────── sections ─────────────────────────────

function renderContract(c: Contract): string {
  const props = c.properties.map((p: NamedProperty) => `
    <li><strong>${esc(p.name)}</strong> <span class="kind">${esc(p.spec.kind)}</span>
      ${p.timingDependent ? '<span class="tag">timing-dependent</span>' : ''}
      <div class="muted">${esc(specText(p.spec))}</div></li>`).join('');
  const chips = (xs: readonly string[]): string => xs.length ? xs.map(x => `<code class="pchip">${esc(x)}</code>`).join(' ') : '<span class="muted">none</span>';
  return `
  <section class="card contract" id="contract">
    <h2>Contract</h2>
    <p class="intent">${esc(c.intent)}</p>
    <div class="cgrid">
      <div><h3>Properties</h3><ul class="props">${props}</ul></div>
      <div>
        <h3>Sinks</h3><p>${chips(c.sinks)}</p><p class="muted small">Where the net may legitimately rest.</p>
        <h3>Sources</h3><p>${chips(c.sources)}</p><p class="muted small">Declared event supplies.</p>
        ${c.scales && c.scales.length ? `<h3>Scales</h3><p>k = ${c.scales.map(esc).join(', ')}</p>` : ''}
      </div>
    </div>
  </section>`;
}

function renderComparison(r: DesignReport): string {
  const rows = r.candidates.map(c => {
    const g = c.gates; const s = c.sensors; const v = verdictCounts(g);
    const cell = (val: string, flag = false): string => `<td class="num${flag ? ' flag' : ''}">${esc(val)}</td>`;
    const routes = [s.routes.enumerable && 'enum', s.routes.ordinary && 'ordinary', s.routes.nu && 'ν', s.routes.timed && 'timed']
      .filter(Boolean).join(', ') || '—';
    return `<tr>
      <th scope="row"><a href="#${slug(c.candidate)}">${esc(c.candidate)}</a></th>
      <td>${badge(g.passed)}</td>
      ${cell(`${v.violated} / ${v.unknown}`, v.violated + v.unknown > 0)}
      ${cell(`${lintCount(g, 'error')} / ${lintCount(g, 'warning')}`, lintCount(g, 'error') > 0)}
      ${cell(num(s.encapsulationViolations), s.encapsulationViolations > 0)}
      ${cell(num(s.resets.crossSubnet), s.resets.crossSubnet > 0)}
      ${cell(num(s.resets.multiToken, 'n/a'), s.resets.multiToken !== 0)}
      ${cell(num(s.essentialPowerArcs), s.essentialPowerArcs > 0)}
      ${cell(pct(s.boundedFraction), s.boundedFraction >= 0 && s.boundedFraction < 1)}
      ${cell(s.stateGrowth.multiplier > 0 ? '×' + round(s.stateGrowth.multiplier) : 'n/a', false)}
      ${cell(num(s.timedWidth), s.timedWidth > 3)}
      ${cell(pct(s.undeclaredSymmetry), s.undeclaredSymmetry > 0)}
      <td>${esc(routes)}</td>
      <td class="num muted">${s.size.places}/${s.size.transitions}/${s.size.arcs}</td>
    </tr>`;
  }).join('');
  return `
  <section class="card" id="compare">
    <h2>Comparison</h2>
    <p class="muted small">Side by side, no single score. Highlighted cells deserve a look; size is context only.</p>
    <div class="table-wrap"><table class="cmp">
      <thead><tr>
        <th>Candidate</th><th>Gates</th><th class="num" title="violated / unknown results">Violated / unknown</th>
        <th class="num" title="lint errors / warnings">Lint err / warn</th>
        <th class="num">Encap. violations</th><th class="num">Cross-subnet resets</th><th class="num">Multi-token resets</th>
        <th class="num">Essential power arcs</th><th class="num">Bounded</th><th class="num">Per-unit growth</th>
        <th class="num">Timed width</th><th class="num">Symmetry</th><th>Routes</th>
        <th class="num" title="places / transitions / arcs; not a quality signal">Size P/T/A</th>
      </tr></thead>
      <tbody>${rows}</tbody>
    </table></div>
  </section>`;
}

function renderCandidate(c: CandidateReport, index: number): string {
  return `
  <section class="card cand ${c.gates.passed ? 'is-pass' : 'is-fail'}" id="${slug(c.candidate)}">
    <header class="chead">
      <h2>${esc(c.candidate)}</h2>${badge(c.gates.passed)}
    </header>
    <p class="why ${c.gates.passed ? 'ok' : 'bad'}">${esc(failureSummary(c.gates))}</p>
    <p class="rationale">${esc(c.rationale)}</p>
    <div class="diagram">
      <div class="petrinet-diagram-viewer lp-host" data-dot-index="${index}" role="img" aria-label="Petri net diagram of ${esc(c.candidate)}">
        <p class="muted small loading">Rendering diagram…</p>
      </div>
      <details class="dotsrc"><summary>DOT source</summary><pre>${esc(c.dot)}</pre></details>
    </div>
    <div class="cols">
      <div class="gates"><h3>Gates</h3>${renderGates(c.gates)}</div>
      <div class="sensors"><h3>Sensors</h3>${renderSensors(c.sensors)}</div>
    </div>
  </section>`;
}

/** What changed from `prev` to `cur`, in short phrases. */
function changes(prev: DesignReport | undefined, cur: DesignReport): string[] {
  if (!prev) return ['First iteration.'];
  const out: string[] = [];
  const before = new Map(prev.candidates.map(c => [c.candidate, c]));
  const after = new Map(cur.candidates.map(c => [c.candidate, c]));
  for (const n of after.keys()) if (!before.has(n)) out.push(`added ${n}`);
  for (const n of before.keys()) if (!after.has(n)) out.push(`dropped ${n}`);
  for (const [n, c] of after) {
    const p = before.get(n);
    if (!p) continue;
    if (p.gates.passed !== c.gates.passed) out.push(`${n} now ${c.gates.passed ? 'passes' : 'fails'}`);
    else if (p.dot !== c.dot && p.dot !== '' && c.dot !== '') out.push(`${n} structure changed`);
    const pv = verdictCounts(p.gates); const cv = verdictCounts(c.gates);
    if (pv.violated !== cv.violated && p.gates.passed === c.gates.passed) out.push(`${n}: violations ${pv.violated} → ${cv.violated}`);
  }
  if (JSON.stringify(prev.contract) !== JSON.stringify(cur.contract)) out.push('contract changed');
  return out.length ? out : ['No verdict changes.'];
}

function renderTimeline(report: DesignReport, history: readonly DesignReport[]): string {
  const byIter = new Map<number, DesignReport>();
  for (const h of history) byIter.set(h.iteration, h);
  byIter.set(report.iteration, report);
  const asc = [...byIter.values()].sort((a, b) => a.iteration - b.iteration);
  const items = asc.map((r, i) => ({ r, changed: changes(asc[i - 1], r) })).reverse();
  return `
  <section class="card" id="timeline">
    <h2>Iterations</h2>
    <ol class="timeline">${items.map(({ r, changed }) => `
      <li class="${r.iteration === report.iteration ? 'current' : ''}">
        <div class="it-head"><strong>Iteration ${r.iteration}</strong>
          <span class="muted small">${esc(fmtTime(r.generatedAt))}</span>
          ${r.iteration === report.iteration ? '<span class="tag">this page</span>' : ''}</div>
        <div class="it-changed">${changed.map(esc).join(' · ')}</div>
        <div class="it-pass small">${r.candidates.map(c => `<span class="mini ${c.gates.passed ? 'pass' : 'fail'}">${esc(c.candidate)}</span>`).join(' ')}</div>
      </li>`).join('')}
    </ol>
  </section>`;
}

function fmtTime(iso: string): string {
  const d = new Date(iso);
  return Number.isNaN(d.getTime()) ? iso : d.toISOString().replace('T', ' ').slice(0, 16) + ' UTC';
}

// ───────────────────────────── page ─────────────────────────────

const CSS = `
:root {
  color-scheme: light dark;
  --bg: #f6f7f9; --surface: #ffffff; --surface-2: #f1f3f6; --text: #16181d; --muted: #5b6270;
  --border: #dde1e7; --accent: #3b5bdb;
  --pass: #1f7a3f; --pass-bg: #e3f4e8; --fail: #b42318; --fail-bg: #fdecea;
  --warn: #9a5b00; --warn-bg: #fff4de; --skip: #6b7280; --skip-bg: #eef0f3;
  --flag-bg: #fff4de; --code-bg: #eef1f5; --diagram-bg: #fafafa;
}
@media (prefers-color-scheme: dark) {
  :root:not([data-theme="light"]) {
    --bg: #111317; --surface: #1a1d23; --surface-2: #222630; --text: #e7e9ee; --muted: #a0a7b4;
    --border: #2e333d; --accent: #8ea2ff;
    --pass: #6fd691; --pass-bg: #173524; --fail: #ff8a80; --fail-bg: #3d1a18;
    --warn: #f3c46b; --warn-bg: #3a2c10; --skip: #a0a7b4; --skip-bg: #262a33;
    --flag-bg: #3a2c10; --code-bg: #262a33; --diagram-bg: #f4f4f5;
  }
}
:root[data-theme="dark"] {
  --bg: #111317; --surface: #1a1d23; --surface-2: #222630; --text: #e7e9ee; --muted: #a0a7b4;
  --border: #2e333d; --accent: #8ea2ff;
  --pass: #6fd691; --pass-bg: #173524; --fail: #ff8a80; --fail-bg: #3d1a18;
  --warn: #f3c46b; --warn-bg: #3a2c10; --skip: #a0a7b4; --skip-bg: #262a33;
  --flag-bg: #3a2c10; --code-bg: #262a33; --diagram-bg: #f4f4f5;
}
* { box-sizing: border-box; }
html { -webkit-text-size-adjust: 100%; }
body {
  margin: 0; background: var(--bg); color: var(--text);
  font: 15px/1.5 system-ui, -apple-system, "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
  overflow-x: hidden;
}
main { max-width: 1200px; margin: 0 auto; padding: 16px; }
h1 { font-size: 1.5rem; margin: 0; line-height: 1.25; }
h2 { font-size: 1.2rem; margin: 0 0 8px; }
h3 { font-size: 1rem; margin: 16px 0 6px; }
h4 { font-size: .9rem; margin: 14px 0 6px; }
a { color: var(--accent); }
code, pre { font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; font-size: .85em; }
code { background: var(--code-bg); padding: 1px 4px; border-radius: 4px; overflow-wrap: anywhere; }
pre { background: var(--code-bg); padding: 12px; border-radius: 6px; overflow: auto; max-height: 320px; }
.muted { color: var(--muted); }
.small { font-size: .85rem; }
.ok { color: var(--pass); } .bad { color: var(--fail); }
.card { background: var(--surface); border: 1px solid var(--border); border-radius: 10px; padding: 16px; margin: 16px 0; min-width: 0; }
.topbar { position: sticky; top: 0; z-index: 5; background: var(--bg); border-bottom: 1px solid var(--border); }
.topbar .inner { max-width: 1200px; margin: 0 auto; padding: 10px 16px; display: flex; flex-wrap: wrap; gap: 8px 16px; align-items: center; }
.topbar .meta { color: var(--muted); font-size: .85rem; }
.status { display: flex; flex-wrap: wrap; gap: 6px; }
.mini { display: inline-block; padding: 1px 8px; border-radius: 999px; font-size: .8rem; text-decoration: none; border: 1px solid transparent; }
.mini.pass { background: var(--pass-bg); color: var(--pass); } .mini.fail { background: var(--fail-bg); color: var(--fail); }
.badge { display: inline-block; padding: 2px 10px; border-radius: 999px; font-size: .8rem; font-weight: 600; white-space: nowrap; }
.badge.pass { background: var(--pass-bg); color: var(--pass); } .badge.fail { background: var(--fail-bg); color: var(--fail); }
.verdict { display: inline-block; padding: 0 8px; border-radius: 4px; font-size: .8rem; font-weight: 600; }
.v-proven { background: var(--pass-bg); color: var(--pass); } .v-violated { background: var(--fail-bg); color: var(--fail); }
.v-unknown { background: var(--warn-bg); color: var(--warn); } .v-skipped { background: var(--skip-bg); color: var(--skip); }
.tag { display: inline-block; font-size: .72rem; font-weight: 500; padding: 0 6px; border-radius: 4px; background: var(--surface-2); color: var(--muted); border: 1px solid var(--border); vertical-align: middle; }
.kind { font-size: .75rem; color: var(--muted); font-family: ui-monospace, Menlo, monospace; }
.intent { font-size: 1.02rem; margin: 0 0 8px; }
.cgrid { display: grid; grid-template-columns: minmax(0, 2fr) minmax(0, 1fr); gap: 16px; }
.props { padding-left: 18px; margin: 0; } .props li { margin: 6px 0; }
.pchip { display: inline-block; margin: 2px 0; }
.table-wrap { overflow-x: auto; -webkit-overflow-scrolling: touch; max-width: 100%; border: 1px solid var(--border); border-radius: 8px; }
table { border-collapse: collapse; width: 100%; font-size: .85rem; }
th, td { padding: 6px 10px; border-bottom: 1px solid var(--border); text-align: left; vertical-align: top; }
thead th { background: var(--surface-2); font-weight: 600; white-space: nowrap; }
tbody tr:last-child td, tbody tr:last-child th { border-bottom: 0; }
td.num, th.num { text-align: right; white-space: nowrap; font-variant-numeric: tabular-nums; }
td.flag { background: var(--flag-bg); color: var(--warn); font-weight: 600; }
table.cmp th[scope=row] { white-space: nowrap; }
tr.r-violated td { background: color-mix(in srgb, var(--fail-bg) 55%, transparent); }
.trace { display: flex; flex-wrap: wrap; gap: 2px 4px; align-items: center; min-width: 220px; }
.trace .arrow { color: var(--muted); }
.trace-d summary { cursor: pointer; }
.note { color: var(--muted); font-size: .8rem; margin-top: 2px; }
.chead { display: flex; align-items: center; gap: 10px; flex-wrap: wrap; }
.chead h2 { margin: 0; overflow-wrap: anywhere; }
.cand.is-pass { border-left: 4px solid var(--pass); } .cand.is-fail { border-left: 4px solid var(--fail); }
.why { margin: 6px 0; font-weight: 600; }
.rationale { margin: 6px 0 12px; }
.diagram { margin: 12px 0; }
.lp-host.petrinet-diagram-viewer { color-scheme: light; color: #111827; --lpv-bg: var(--diagram-bg); height: 60vh; min-height: 320px; max-height: 620px; }
.lp-host .loading { padding: 12px; }
.lp-host .err { padding: 12px; color: #991b1b; }
.dotsrc summary { cursor: pointer; font-size: .85rem; color: var(--muted); margin-top: 6px; }
.cols { display: grid; grid-template-columns: minmax(0, 1.25fr) minmax(0, 1fr); gap: 20px; }
.lint { list-style: none; padding: 0; margin: 0; }
.lint li { padding: 6px 8px; border-radius: 6px; margin: 4px 0; background: var(--surface-2); }
.lint .sev { font-size: .72rem; font-weight: 700; text-transform: uppercase; }
.lint .sev-error .sev { color: var(--fail); } .lint .sev-warning .sev { color: var(--warn); }
.sgrid { display: grid; gap: 10px; }
.sgroup { background: var(--surface-2); border-radius: 8px; padding: 8px 12px; }
.sgroup h4 { margin: 2px 0; } .sgroup p { margin: 2px 0 6px; }
.sgroup dl { margin: 0; }
.srow { display: grid; grid-template-columns: minmax(0, 1fr) auto; gap: 0 10px; padding: 5px 0; border-top: 1px solid var(--border); }
.srow dt { font-weight: 500; } .srow .sval { margin: 0; text-align: right; font-variant-numeric: tabular-nums; font-weight: 600; }
.srow .smeaning { grid-column: 1 / -1; margin: 0; color: var(--muted); font-size: .8rem; }
.srow.flag .sval { color: var(--warn); }
.srow.flag dt::after { content: " ●"; color: var(--warn); font-size: .7em; vertical-align: middle; }
.size .sizeline { font-variant-numeric: tabular-nums; margin: 4px 0; }
.timeline { list-style: none; padding: 0; margin: 0; }
.timeline li { border-left: 3px solid var(--border); padding: 4px 0 10px 12px; }
.timeline li.current { border-left-color: var(--accent); }
.it-head { display: flex; gap: 8px; align-items: baseline; flex-wrap: wrap; }
.it-changed { margin: 2px 0 4px; }
@media (max-width: 760px) {
  .cgrid, .cols { grid-template-columns: minmax(0, 1fr); }
  .lp-host.petrinet-diagram-viewer { height: 55vh; min-height: 280px; }
  h1 { font-size: 1.25rem; }
  .topbar { position: static; }
}
`;

const MOUNT = `
(function () {
  var dots = JSON.parse(document.getElementById('lp-dots').textContent);
  var hosts = Array.prototype.slice.call(document.querySelectorAll('.lp-host[data-dot-index]'));
  var queue = Promise.resolve();
  function fail(host, e) {
    host.innerHTML = '';
    var p = document.createElement('p');
    p.className = 'err';
    p.textContent = 'Diagram could not render: ' + (e && e.message ? e.message : e) + '. The DOT source is below.';
    host.appendChild(p);
  }
  function mount(host) {
    if (host.getAttribute('data-mounted')) return;
    host.setAttribute('data-mounted', '1');
    var dot = dots[Number(host.getAttribute('data-dot-index'))];
    queue = queue.then(function () {
      if (!window.LibpetriViewer || typeof window.LibpetriViewer.mount !== 'function') throw new Error('viewer bundle missing');
      return window.LibpetriViewer.mount(dot, host, { chrome: true });
    }).catch(function (e) { console.error('[design] viewer mount failed', e); fail(host, e); });
  }
  if ('IntersectionObserver' in window) {
    var io = new IntersectionObserver(function (entries) {
      entries.forEach(function (en) { if (en.isIntersecting) { io.unobserve(en.target); mount(en.target); } });
    }, { rootMargin: '400px 0px' });
    hosts.forEach(function (h) { io.observe(h); });
    // Visible diagrams go first; the rest follow in page order so none is left unrendered
    // (some hosts, e.g. headless or backgrounded tabs, never report intersections).
    setTimeout(function () { hosts.forEach(mount); }, 1200);
  } else {
    hosts.forEach(mount);
  }
})();
`;

/** JSON for an inline <script type="application/json">: no sequence can close the element. */
function inlineJson(x: unknown): string {
  return JSON.stringify(x).replace(/</g, '\\u003c').replace(/>/g, '\\u003e').replace(/&/g, '\\u0026');
}

export function renderDesignPage(report: DesignReport, history?: DesignReport[]): string {
  const { js, css } = viewerAssets();
  const title = pageTitle(report.contract);
  const passing = report.candidates.filter(c => c.gates.passed).length;
  const status = report.candidates.map(c =>
    `<a class="mini ${c.gates.passed ? 'pass' : 'fail'}" href="#${slug(c.candidate)}">${c.gates.passed ? '✓' : '✕'} ${esc(c.candidate)}</a>`).join('');
  const timeline = history ? renderTimeline(report, history) : '';
  return `<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="generator" content="libpetri design harness">
<title>${esc(title)}</title>
<style>${css}</style>
<style>${CSS}</style>
</head>
<body>
<div class="topbar"><div class="inner">
  <strong>${esc(report.contract.name)}</strong>
  <span class="meta">Iteration ${report.iteration} · ${esc(fmtTime(report.generatedAt))} · ${passing} of ${report.candidates.length} pass</span>
  <nav class="status" aria-label="Candidates">${status}</nav>
</div></div>
<main>
  <h1>${esc(report.contract.name)}: design candidates</h1>
  ${renderContract(report.contract)}
  ${timeline}
  ${renderComparison(report)}
  ${report.candidates.map(renderCandidate).join('')}
  <p class="muted small">Generated by the libpetri design harness. Verdicts come from the gates; sensors describe mechanism and are not combined into a score.</p>
</main>
<script type="application/json" id="lp-dots">${inlineJson(report.candidates.map(c => c.dot))}</script>
<script>${js}</script>
<script>${MOUNT}</script>
</body>
</html>
`;
}
