/**
 * Locates and reads the conformance corpus and runs every net of it through the TypeScript
 * verifier under the route setups of `rust/libpetri-verification/tests/route_agreement.rs`,
 * holding each verdict against the Lean reference's expected file (README "Conformance rule").
 */
import { existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { SmtVerifier } from '../../../src/verification/smt-verifier.js';
import { loadNet, type LoadedNet } from './loader.js';
import {
  checkConformance,
  checkDefaultPassConformance,
  stripBranch,
  type ExpectedEntry,
  type Finding,
  type LangResult,
} from './reference.js';

// ======================================================================
// Locating and reading
// ======================================================================

/** `LIBPETRI_CONFORMANCE_DIR`, else `spec/verification-fixtures/conformance` found upward. */
export function locateCorpus(): string | null {
  const env = process.env['LIBPETRI_CONFORMANCE_DIR'];
  if (env) return resolve(env);
  let dir = dirname(fileURLToPath(import.meta.url));
  for (let depth = 0; depth < 10; depth++) {
    const candidate = join(dir, 'spec', 'verification-fixtures', 'conformance');
    if (existsSync(candidate)) return candidate;
    const parent = dirname(dir);
    if (parent === dir) break;
    dir = parent;
  }
  return null;
}

export interface ExpectedFile {
  readonly id: string;
  readonly reference: string;
  readonly complete: boolean;
  readonly results: readonly ExpectedEntry[];
}

export interface CorpusEntry {
  readonly id: string;
  readonly netPath: string;
  readonly expectedPath: string;
}

export interface Corpus {
  readonly dir: string;
  /** Nets with an expected file, sorted by file name. */
  readonly entries: readonly CorpusEntry[];
  /** Net ids without an expected file (not checked). */
  readonly missingExpected: readonly string[];
  /** Why the corpus cannot be run, when it cannot. */
  readonly skipReason: string | null;
}

export function readCorpus(dir: string | null): Corpus {
  if (dir === null) {
    return { dir: '', entries: [], missingExpected: [], skipReason: 'spec/verification-fixtures/conformance not found' };
  }
  const netsDir = join(dir, 'nets');
  const nets = existsSync(netsDir) ? readdirSync(netsDir).filter(f => f.endsWith('.json')).sort() : [];
  if (nets.length === 0) {
    return { dir, entries: [], missingExpected: [], skipReason: `no corpus nets in ${netsDir} yet` };
  }
  const entries: CorpusEntry[] = [];
  const missingExpected: string[] = [];
  for (const file of nets) {
    const id = file.slice(0, -'.json'.length);
    const expectedPath = join(dir, 'expected', file);
    if (existsSync(expectedPath)) entries.push({ id, netPath: join(netsDir, file), expectedPath });
    else missingExpected.push(id);
  }
  return {
    dir,
    entries,
    missingExpected,
    skipReason: entries.length === 0
      ? `${nets.length} corpus nets but no expected/<id>.json yet (written by \`lake exe reference\`)`
      : null,
  };
}

export function readExpected(path: string): ExpectedFile {
  const raw = JSON.parse(readFileSync(path, 'utf8'));
  for (const r of raw.results ?? []) {
    if (!['proven', 'violated', 'unknown'].includes(r.verdict)) {
      throw new Error(`${path}: unknown verdict ${JSON.stringify(r.verdict)} for ${r.property}`);
    }
  }
  return { id: raw.id, reference: raw.reference, complete: raw.complete, results: raw.results ?? [] };
}

// ======================================================================
// Route setups (route_agreement.rs CONFIGS)
// ======================================================================

export interface RouteConfig {
  readonly name: string;
  readonly enumBudget: number;
  readonly linearBound: boolean;
  readonly phases: boolean;
  /** Whether the setup needs z3 by construction (enumeration off). */
  readonly smt: boolean;
  /** The atomic pass (all four rules) or the default, split pass (rules 1, 3, 4). */
  readonly atomic: boolean;
}

export const ROUTE_CONFIGS: readonly RouteConfig[] = [
  { name: 'enum', enumBudget: 5_000, linearBound: true, phases: true, smt: false, atomic: true },
  { name: 'smt+lb', enumBudget: 0, linearBound: true, phases: true, smt: true, atomic: true },
  { name: 'smt-lb', enumBudget: 0, linearBound: false, phases: true, smt: true, atomic: true },
  { name: 'ic3', enumBudget: 0, linearBound: false, phases: false, smt: true, atomic: true },
  { name: 'enum/split', enumBudget: 5_000, linearBound: true, phases: true, smt: false, atomic: false },
  { name: 'smt+lb/split', enumBudget: 0, linearBound: true, phases: true, smt: true, atomic: false },
  { name: 'smt-lb/split', enumBudget: 0, linearBound: false, phases: true, smt: true, atomic: false },
  { name: 'ic3/split', enumBudget: 0, linearBound: false, phases: false, smt: true, atomic: false },
];

async function runConfig(loaded: LoadedNet, index: number, cfg: RouteConfig): Promise<LangResult> {
  const lp = loaded.properties[index]!;
  const v = SmtVerifier.forNet(loaded.net)
    // The Lean reference fires atomically and does not model the in-flight split of VER-004:
    // the atomic pass compares on that reading, the default pass on the caller's.
    .assumeAtomicFiring(cfg.atomic)
    .initialMarking(loaded.initialMarking)
    .property(lp.property)
    .enumerationMaxClasses(cfg.enumBudget)
    .linearBound(cfg.linearBound)
    .stateEquationPhase(cfg.phases)
    .firingBound(cfg.phases)
    .certificateCheck(true)
    .counterexampleReplay(true)
    .timeout(4_000)
    .totalBudget(12_000);
  if (lp.sinks.length > 0) v.sinkPlaces(...lp.sinks);
  const r = await v.verify();
  switch (r.verdict.type) {
    case 'proven': return { verdict: 'proven', trace: [], traced: false };
    case 'violated': {
      const trace = [...r.counterexampleTransitions];
      // README clarification 6: a trace of one marking and no step is the initial marking
      // itself (`[]`); a violation with neither is untraced — a rule-3 finding.
      return {
        verdict: 'violated', trace, traced: trace.length > 0 || r.counterexampleTrace.length === 1,
        split: !cfg.atomic && r.report.includes('In-flight actions (VER-004):'),
        confirmed: r.counterexampleConfirmed,
      };
    }
    case 'unknown': return { verdict: 'unknown', trace: [], traced: false, reason: r.verdict.reason };
  }
}

// ======================================================================
// The run
// ======================================================================

export interface RouteStats {
  proven: number;
  violated: number;
  unknown: number;
  /** Violated verdicts with no firing sequence: rule-3 findings (README clarification 6). */
  untraced: number;
  /** Default pass: violated where the reference proves the property (rule 2 skipped). */
  violatedWhereReferenceProved: number;
  /** Default pass: traces of split nets, not replayed by the reference. */
  splitTraces: number;
  /** Of those, the ones the abstract replay did not confirm. */
  splitUnconfirmed: number;
  reasons: Map<string, number>;
}

export interface CorpusReport {
  readonly findings: Finding[];
  readonly stats: Map<string, RouteStats>;
  readonly nets: number;
  readonly queries: number;
  readonly skippedConfigs: readonly string[];
  /** `<net>/<property>` of each mutual exclusion over 3+ places (two-place API, clarification 1). */
  readonly skippedProperties: readonly string[];
}

/** An unknown reason's first line, digits folded, so like reasons group. */
function reasonKey(reason: string | undefined): string {
  return (reason ?? '(no reason)').split('\n')[0]!.replace(/\d+/g, 'N').slice(0, 140);
}

export async function runCorpus(
  corpus: Corpus,
  opts: { readonly z3: boolean; readonly dumpDir?: string | undefined },
): Promise<CorpusReport> {
  const configs = ROUTE_CONFIGS.filter(c => opts.z3 || !c.smt);
  const skippedConfigs = ROUTE_CONFIGS.filter(c => !configs.includes(c)).map(c => c.name);
  const stats = new Map<string, RouteStats>(
    configs.map(c => [c.name, {
      proven: 0, violated: 0, unknown: 0, untraced: 0, violatedWhereReferenceProved: 0, splitTraces: 0,
      splitUnconfirmed: 0, reasons: new Map(),
    }]),
  );
  const findings: Finding[] = [];
  const skippedProperties: string[] = [];
  let queries = 0;
  for (const entry of corpus.entries) {
    const loaded = loadNet(JSON.parse(readFileSync(entry.netPath, 'utf8')));
    if (loaded.spec.id !== entry.id) throw new Error(`${entry.netPath}: id '${loaded.spec.id}' does not match file name`);
    skippedProperties.push(...loaded.skipped.map(ps => `${entry.id}/${ps.id}`));
    const expected = readExpected(entry.expectedPath);
    if (expected.id !== entry.id) throw new Error(`${entry.expectedPath}: id '${expected.id}' does not match file name`);
    const byProp = new Map(expected.results.map(r => [r.property, r]));
    const dump: { property: string; trace: string[] }[] = [];
    const dumped = new Set<string>();
    for (const [i, lp] of loaded.properties.entries()) {
      queries++;
      if (!byProp.has(lp.spec.id)) {
        findings.push({
          kind: 'STALE EXPECTED', net: entry.id, property: lp.spec.id, route: '-',
          detail: 'no reference verdict (expected/ is stale)',
        });
        continue;
      }
      for (const cfg of configs) {
        const result = await runConfig(loaded, i, cfg);
        const s = stats.get(cfg.name)!;
        s[result.verdict]++;
        if (result.verdict === 'violated' && !result.traced) s.untraced++;
        if (result.verdict === 'unknown') {
          const k = reasonKey(result.reason);
          s.reasons.set(k, (s.reasons.get(k) ?? 0) + 1);
        }
        const expectedEntry = byProp.get(lp.spec.id);
        if (cfg.atomic) {
          findings.push(...checkConformance(loaded.spec, lp.spec, cfg.name, result, expectedEntry));
        } else {
          findings.push(...checkDefaultPassConformance(loaded.spec, lp.spec, cfg.name, result, expectedEntry));
          if (result.verdict === 'violated' && expectedEntry?.verdict === 'proven') s.violatedWhereReferenceProved++;
        }
        if (result.verdict === 'violated' && result.traced && result.split === true) {
          // Names completion steps the reference does not have: counted, never dumped.
          s.splitTraces++;
          if (result.confirmed === false) s.splitUnconfirmed++;
        } else if (result.verdict === 'violated' && result.traced) {
          const trace = result.trace.map(n => stripBranch(loaded.spec, n));
          const k = JSON.stringify([lp.spec.id, trace]);
          if (!dumped.has(k)) {
            dumped.add(k);
            dump.push({ property: lp.spec.id, trace });
          }
        }
      }
    }
    // Only nets with at least one traced violation get a dump file, as in Rust's conformance.rs.
    if (opts.dumpDir && dump.length > 0) {
      mkdirSync(opts.dumpDir, { recursive: true });
      writeFileSync(join(opts.dumpDir, `${entry.id}.traces.json`), JSON.stringify(dump, null, 2) + '\n');
    }
  }
  return { findings, stats, nets: corpus.entries.length, queries, skippedConfigs, skippedProperties };
}

export function renderReport(corpus: Corpus, report: CorpusReport): string {
  const lines = [
    `conformance (typescript): ${report.nets} nets / ${report.queries} properties from ${corpus.dir}` +
      (corpus.missingExpected.length > 0 ? ` (${corpus.missingExpected.length} nets lack an expected file, not checked)` : ''),
  ];
  if (report.skippedConfigs.length > 0) {
    lines.push(`  skipped (z3 not available): ${report.skippedConfigs.join(', ')}`);
  }
  if (report.skippedProperties.length > 0) {
    lines.push(
      `  skipped ${report.skippedProperties.length} mutual-exclusion propert(ies) over 3+ places ` +
        `(two-place API): ${report.skippedProperties.join(', ')}`,
    );
  }
  for (const [name, s] of report.stats) {
    lines.push(
      `  ${name.padEnd(12)} proven ${s.proven} / violated ${s.violated} / unknown ${s.unknown}` +
        ` | violated without a trace ${s.untraced}` +
        (name.endsWith('/split')
          ? ` | violated-where-reference-proved ${s.violatedWhereReferenceProved}` +
            ` | traces of split nets ${s.splitTraces} (unconfirmed by the abstract replay ${s.splitUnconfirmed})`
          : ''),
    );
    const top = [...s.reasons].sort((a, b) => b[1] - a[1] || (a[0] < b[0] ? -1 : 1)).slice(0, 8);
    for (const [k, n] of top) lines.push(`    unknown x${n}: ${k}`);
  }
  lines.push(`  findings: ${report.findings.length}`);
  return lines.join('\n');
}
