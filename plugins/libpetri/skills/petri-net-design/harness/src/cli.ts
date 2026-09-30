/**
 * Design harness CLI.
 *
 *   npm run design -- evaluate --contract <contract.ts> --candidates <a.ts> [b.ts ...]
 *                              [--out out/] [--iteration n] [--budget-ms n]
 *   npm run design -- compare --design <out/cand.dot> --impl <impl.dot>
 *
 * `evaluate` gates and measures every candidate, then writes report.json, design.html (the artifact
 * page), <candidate>.dot, and appends to history.json so the page shows the iteration timeline.
 * `compare` checks an implementation's DOT export against the verified design's; exit 1 if not equal.
 */
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { basename, join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { renderDesignPage } from './artifact.js';
import { candidateDot } from './dot.js';
import { compareDot } from './equivalence.js';
import { runGates } from './gates.js';
import { measure } from './sensors.js';
import type { Candidate, CandidateReport, Contract, DesignReport, Verdict } from './types.js';

interface Args { readonly command: string; readonly flags: Map<string, string[]> }

function parseArgs(argv: readonly string[]): Args {
  const [command = 'help', ...rest] = argv;
  const flags = new Map<string, string[]>();
  let current: string | null = null;
  for (const a of rest) {
    if (a.startsWith('--')) {
      const eq = a.indexOf('=');
      if (eq > 0) { flags.set(a.slice(2, eq), [a.slice(eq + 1)]); current = null; continue; }
      current = a.slice(2);
      if (!flags.has(current)) flags.set(current, []);
    } else if (current) {
      flags.get(current)!.push(a);
    } else {
      throw new Error(`unexpected argument '${a}'`);
    }
  }
  return { command, flags };
}

function one(flags: Map<string, string[]>, name: string): string | undefined {
  const v = flags.get(name);
  if (v && v.length > 1) throw new Error(`--${name} takes one value`);
  return v?.[0];
}

function required(flags: Map<string, string[]>, name: string): string {
  const v = one(flags, name);
  if (!v) throw new Error(`missing --${name}`);
  return v;
}

function intFlag(flags: Map<string, string[]>, name: string): number | undefined {
  const v = one(flags, name);
  if (v === undefined) return undefined;
  const n = Number(v);
  if (!Number.isInteger(n) || n < 0) throw new Error(`--${name} must be a non-negative integer`);
  return n;
}

async function importDefault(file: string): Promise<unknown> {
  const mod = (await import(pathToFileURL(resolve(file)).href)) as { default?: unknown };
  if (mod.default === undefined) throw new Error(`${file} has no default export`);
  return mod.default;
}

function isCandidate(x: unknown): x is Candidate {
  return typeof x === 'object' && x !== null && typeof (x as Candidate).name === 'string' && typeof (x as Candidate).build === 'function';
}

function fileSafe(name: string): string {
  return name.replace(/[^A-Za-z0-9._-]+/g, '_');
}

const USAGE = `usage:
  npm run design -- evaluate --contract <contract.ts> --candidates <a.ts> [b.ts ...]
                             [--out out/] [--iteration n] [--budget-ms n]
  npm run design -- compare --design <out/cand.dot> --impl <impl.dot>`;

async function evaluate(flags: Map<string, string[]>): Promise<number> {
  const contractFile = required(flags, 'contract');
  const candidateFiles = flags.get('candidates') ?? [];
  if (candidateFiles.length === 0) throw new Error('missing --candidates');
  const outDir = resolve(one(flags, 'out') ?? 'out');
  const budgetMs = intFlag(flags, 'budget-ms');
  // Experiment condition: gates only — no sensors and no lint warnings reach the designer.
  const gatesOnly = flags.has('gates-only');

  const contract = (await importDefault(contractFile)) as Contract;
  if (!contract || typeof contract.name !== 'string' || !Array.isArray(contract.properties)) {
    throw new Error(`${contractFile}: default export is not a Contract`);
  }
  const candidates: Candidate[] = [];
  for (const f of candidateFiles) {
    const d = await importDefault(f);
    const list = Array.isArray(d) ? d : [d];
    for (const c of list) {
      if (!isCandidate(c)) throw new Error(`${f}: default export is not a Candidate or Candidate[]`);
      if (candidates.some(x => x.name === c.name)) throw new Error(`duplicate candidate name '${c.name}'`);
      candidates.push(c);
    }
  }

  mkdirSync(outDir, { recursive: true });
  const historyFile = join(outDir, 'history.json');
  let history: DesignReport[] = [];
  if (existsSync(historyFile)) {
    try { history = JSON.parse(readFileSync(historyFile, 'utf8')) as DesignReport[]; }
    catch { process.stderr.write(`warning: ${historyFile} is not valid JSON; starting a new history\n`); }
  }
  const iteration = intFlag(flags, 'iteration') ?? (history.reduce((m, h) => Math.max(m, h.iteration), 0) + 1);

  const reports: CandidateReport[] = [];
  for (const c of candidates) {
    const t0 = Date.now();
    const tty = process.stdout.isTTY === true;
    if (tty) process.stdout.write(`… ${c.name}`);
    let built: ReturnType<Candidate['build']>;
    try {
      built = c.build(1);
    } catch (e) {
      // A candidate libpetri refuses to build fails the gate with the builder's message; it is a
      // finding, not a harness crash (e.g. an arc on a port place composition bound away, MOD-027).
      reports.push(buildErrorReport(c, e));
      if (tty) process.stdout.write(`\r\x1b[K`);
      summaryLine(reports[reports.length - 1]!, Date.now() - t0);
      continue;
    }
    const dot = candidateDot(built.net);
    const fullGates = await runGates(contract, c, budgetMs === undefined ? undefined : { budgetMs });
    const gates = gatesOnly ? { ...fullGates, lint: fullGates.lint.filter(l => l.severity === 'error') } : fullGates;
    const sensors = gatesOnly ? emptySensors() : await measure(contract, c);
    reports.push({ candidate: c.name, rationale: c.rationale, gates, sensors, dot });
    writeFileSync(join(outDir, `${fileSafe(c.name)}.dot`), dot);
    if (tty) process.stdout.write(`\r\x1b[K`);
    summaryLine(reports[reports.length - 1]!, Date.now() - t0);
  }

  const report: DesignReport = {
    contract: jsonSafe(contract),
    generatedAt: new Date().toISOString(),
    iteration,
    candidates: reports,
    passing: reports.filter(r => r.gates.passed).map(r => r.candidate),
  };
  // History keeps verdicts and sensors; DOT is only needed for the current page (keeps history small).
  const slim: DesignReport = { ...report, candidates: report.candidates.map(c => ({ ...c, dot: '' })) };
  history = [...history.filter(h => h.iteration !== iteration), slim].sort((a, b) => a.iteration - b.iteration);

  writeFileSync(join(outDir, 'report.json'), JSON.stringify(report, null, 2));
  writeFileSync(historyFile, JSON.stringify(history, null, 2));
  const html = renderDesignPage(report, history);
  writeFileSync(join(outDir, 'design.html'), html);

  console.log(`\niteration ${iteration}: ${report.passing.length} of ${reports.length} pass` +
    (report.passing.length ? ` (${report.passing.join(', ')})` : ''));
  console.log(`wrote ${rel(join(outDir, 'design.html'))} (${(html.length / 1e6).toFixed(1)} MB), report.json, history.json, ` +
    reports.map(r => `${fileSafe(r.candidate)}.dot`).join(', '));
  return 0;
}

/** Contracts are plain data; strip anything JSON cannot carry so report.json round-trips. */
function jsonSafe<T>(x: T): T {
  return JSON.parse(JSON.stringify(x)) as T;
}

function rel(p: string): string {
  const cwd = process.cwd() + '/';
  return p.startsWith(cwd) ? p.slice(cwd.length) : p;
}

function summaryLine(r: CandidateReport, elapsed: number): void {
  const count: Record<Verdict, number> = { proven: 0, violated: 0, unknown: 0, skipped: 0 };
  const bad: string[] = [];
  for (const s of r.gates.smallScope) for (const x of s.results) {
    count[x.verdict]++;
    if ((x.verdict === 'violated' || x.verdict === 'unknown') && !bad.some(b => b.startsWith(x.property + ' '))) {
      bad.push(`${x.property} ${x.verdict}@k=${s.k}`);
    }
  }
  for (const s of r.gates.compositional) for (const x of s.results) {
    count[x.verdict]++;
    if (x.verdict === 'violated' || x.verdict === 'unknown') bad.push(`${s.subnet}:${x.property} ${x.verdict}`);
  }
  const errs = r.gates.lint.filter(l => l.severity === 'error');
  const s = r.sensors;
  const hideSensors = s.stateGrowth.k1 === -1 && s.size.places === 0;
  const mark = r.gates.passed ? 'PASS' : 'FAIL';
  console.log(`${mark}  ${r.candidate}  (${(elapsed / 1000).toFixed(1)} s)`);
  console.log(`      proven ${count.proven}, violated ${count.violated}, unknown ${count.unknown}, skipped ${count.skipped}; ` +
    `lint ${errs.length} error(s), ${r.gates.lint.length - errs.length} warning(s)`);
  for (const b of bad) console.log(`      ✕ ${b}`);
  for (const e of errs) console.log(`      ✕ lint ${e.rule}: ${e.message}`);
  if (hideSensors) return;
  console.log(`      encap ${s.encapsulationViolations}, cross-subnet resets ${s.resets.crossSubnet}, ` +
    `multi-token resets ${s.resets.multiToken}, essential power arcs ${s.essentialPowerArcs}, ` +
    `growth ×${s.stateGrowth.multiplier.toFixed(1)}  [size ${s.size.places}P/${s.size.transitions}T, context only]`);
}

function compare(flags: Map<string, string[]>): number {
  const designFile = required(flags, 'design');
  const implFile = required(flags, 'impl');
  const result = compareDot(readFileSync(designFile, 'utf8'), readFileSync(implFile, 'utf8'));
  if (result.equal) {
    console.log(`EQUAL  ${basename(implFile)} is structurally identical to the design ${basename(designFile)}`);
    return 0;
  }
  console.log(`DIFFERENT  ${basename(implFile)} vs design ${basename(designFile)}: ${result.differences.length} difference(s)`);
  for (const d of result.differences) console.log(`  - ${d}`);
  return 1;
}

async function main(argv: readonly string[]): Promise<number> {
  const { command, flags } = parseArgs(argv);
  switch (command) {
    case 'evaluate': return evaluate(flags);
    case 'compare': return compare(flags);
    case 'help': case '--help': case '-h': console.log(USAGE); return 0;
    default: console.error(`unknown command '${command}'\n${USAGE}`); return 2;
  }
}

main(process.argv.slice(2)).then(
  code => { process.exitCode = code; },
  (e: unknown) => { console.error(`error: ${e instanceof Error ? e.message : String(e)}\n${USAGE}`); process.exitCode = 2; },
);


/** Report for a candidate that does not build: failed gate, empty sensor profile. */
export function buildErrorReport(c: Candidate, e: unknown): CandidateReport {
  const message = e instanceof Error ? e.message : String(e);
  const none = -1;
  return {
    candidate: c.name,
    rationale: c.rationale,
    dot: '',
    gates: {
      lint: [{ rule: 'build-error', severity: 'error', message: `libpetri rejected the net: ${message}` }],
      smallScope: [],
      compositional: [],
      passed: false,
    },
    sensors: emptySensors(),
  };
}

/** Sensor profile carrying no information (build errors, and the gates-only experiment condition). */
export function emptySensors(): CandidateReport['sensors'] {
  const none = -1;
  return {
      size: { places: 0, transitions: 0, arcs: 0 },
      resets: { count: 0, blast: 0, reach: 0, multiToken: none, crossSubnet: 0 },
      encapsulationViolations: 0,
      essentialPowerArcs: none,
      boundedFraction: none,
      undeclaredSymmetry: 0,
      routes: { ordinary: false, enumerable: false, nu: false, timed: false },
      stateGrowth: { k1: none, k2: none, multiplier: none },
      timedWidth: none,
  };
}
