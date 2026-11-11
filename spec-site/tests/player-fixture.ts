/**
 * Test fixture for the diagram and player tests: the authored situations of
 * `spec/situations/*.json` with their Lean replays, normalised to the model the way the
 * contracts describe (defaults filled, `fired` / `blocked` turned into `kind`). This is a small
 * test-only reader; the site's own reader is `src/gen/inputs/situations.ts`.
 */
import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath, URL as NodeURL } from 'node:url';
import type {
  BlockReason,
  CorpusNet,
  InputArc,
  Marking,
  NetTransition,
  OutputSpec,
  ReplayResult,
  ReplayStep,
  Situation,
  SituationEntry,
  SituationGroup,
  Timing,
} from '../src/model.js';

/* The raw JSON is untyped; these readers narrow it field by field. */
type Json = Record<string, unknown>;

const obj = (v: unknown): Json => {
  if (typeof v !== 'object' || v === null || Array.isArray(v)) throw new Error('expected an object');
  return v as Json; // narrowed by the check above
};
const arr = (v: unknown): readonly unknown[] => (v === undefined ? [] : Array.isArray(v) ? v : []);
const str = (v: unknown): string => {
  if (typeof v !== 'string') throw new Error('expected a string');
  return v;
};
const int = (v: unknown, fallback = 0): number => (typeof v === 'number' ? v : fallback);

function marking(v: unknown): Marking {
  const out: Record<string, number> = {};
  for (const [k, n] of Object.entries(v === undefined ? {} : obj(v)).sort(([a], [b]) => (a < b ? -1 : 1))) {
    if (typeof n === 'number' && n > 0) out[k] = n;
  }
  return out;
}

function inputArc(v: unknown): InputArc {
  const o = obj(v);
  const place = str(o['place']);
  switch (o['kind']) {
    case 'exactly':
      return { kind: 'exactly', place, n: int(o['n']) };
    case 'atLeast':
      return { kind: 'atLeast', place, n: int(o['n']) };
    case 'all':
      return { kind: 'all', place };
    default:
      return { kind: 'one', place };
  }
}

function output(v: unknown): OutputSpec {
  const o = obj(v);
  switch (o['type']) {
    case 'and':
      return { type: 'and', children: arr(o['children']).map(output) };
    case 'xor':
      return { type: 'xor', children: arr(o['children']).map(output) };
    case 'timeout':
      return { type: 'timeout', afterMs: int(o['afterMs']), child: output(o['child']) };
    case 'forward':
      return { type: 'forward', from: str(o['from']), to: str(o['to']) };
    default:
      return { type: 'place', place: str(o['place']) };
  }
}

function timing(v: unknown): Timing | null {
  if (v === undefined || v === null) return null;
  const o = obj(v);
  const ms = (k: string): number | null => (typeof o[k] === 'number' ? o[k] : null);
  return { kind: str(o['kind']) as Timing['kind'], earliestMs: ms('earliestMs'), latestMs: ms('latestMs') }; // kind checked by the builder
}

function transition(v: unknown): NetTransition {
  const o = obj(v);
  return {
    name: str(o['name']),
    inputs: arr(o['inputs']).map(inputArc),
    inhibitors: arr(o['inhibitors']).map(str),
    reads: arr(o['reads']).map(str),
    resets: arr(o['resets']).map(str),
    output: o['output'] === undefined || o['output'] === null ? null : output(o['output']),
    priority: int(o['priority']),
    timing: timing(o['timing']),
  };
}

export function corpusNet(o: Json): CorpusNet {
  return {
    places: arr(o['places']).map(str),
    marking: marking(o['marking']),
    transitions: arr(o['transitions']).map(transition),
    properties: [],
  };
}

function reason(v: unknown): BlockReason {
  const o = obj(v);
  switch (o['kind']) {
    case 'inputShort': {
      const a = obj(o['arc']);
      return {
        kind: 'inputShort',
        place: str(o['place']),
        arc: { kind: str(a['kind']) as InputArc['kind'], n: typeof a['n'] === 'number' ? a['n'] : null }, // Lean writes the four kinds
        need: int(o['need']),
        have: int(o['have']),
      };
    }
    case 'inhibitorMarked':
      return { kind: 'inhibitorMarked', place: str(o['place']), count: int(o['count']) };
    case 'readEmpty':
      return { kind: 'readEmpty', place: str(o['place']) };
    case 'noSuchBranch':
      return { kind: 'noSuchBranch', branch: int(o['branch']), timeout: o['timeout'] === true };
    default:
      return { kind: 'unknownTransition' };
  }
}

function replayStep(v: unknown): ReplayStep {
  const o = obj(v);
  const base = { index: int(o['index']), fire: str(o['fire']), branch: int(o['branch']), timeout: o['timeout'] === true };
  if (o['fired'] === true) return { kind: 'fired', ...base, marking: marking(o['marking']) };
  return { kind: 'blocked', ...base, reason: reason(o['reason']), requirement: str(o['requirement']), message: str(o['message']) };
}

/**
 * The repository root. Computed here with Node's own URL class (not `src/gen/paths.ts`): under
 * the happy-dom environment the global `URL` is the DOM one, which `fileURLToPath` refuses.
 */
export const REPO: string = fileURLToPath(new NodeURL('../../', import.meta.url));

export function situationsDir(): string {
  return join(REPO, 'spec', 'situations');
}

/** Slugs of the authored situations, sorted. */
export function situationSlugs(): readonly string[] {
  return readdirSync(situationsDir())
    .filter((f) => f.endsWith('.json'))
    .map((f) => f.slice(0, -'.json'.length))
    .sort();
}

/** One authored situation and its replay (null when `replay` is false). */
export function loadSituation(slug: string): { situation: Situation; result: ReplayResult | null } {
  const o = obj(JSON.parse(readFileSync(join(situationsDir(), `${slug}.json`), 'utf8')));
  const replay = o['replay'] !== false;
  const situation: Situation = {
    slug,
    title: typeof o['title'] === 'string' ? o['title'] : slug,
    text: typeof o['text'] === 'string' ? o['text'] : '',
    group: (typeof o['group'] === 'string' ? o['group'] : 'Firing') as SituationGroup, // checked by the site's reader
    cites: arr(o['cites']).map(str),
    replay,
    notReplayed: replay ? null : (str(o['notReplayed']) as Situation['notReplayed']), // checked by the site's reader
    net: corpusNet(o),
    steps: arr(o['steps']).map((sv) => {
      const st = obj(sv);
      return { fire: str(st['fire']), branch: int(st['branch']), timeout: st['timeout'] === true, text: typeof st['text'] === 'string' ? st['text'] : null, expect: st['expect'] === 'blocked' ? 'blocked' as const : 'fired' as const };
    }),
  };
  if (!replay) return { situation, result: null };
  const e = obj(JSON.parse(readFileSync(join(situationsDir(), 'expected', `${slug}.json`), 'utf8')));
  const result: ReplayResult = {
    slug,
    reference: str(e['reference']),
    initial: marking(e['initial']),
    complete: e['complete'] === true,
    steps: arr(e['steps']).map(replayStep),
  };
  return { situation, result };
}

/** A `SituationEntry` as the site would hold it (rules empty: the player does not read them). */
export function loadEntry(slug: string, diagram = true): SituationEntry {
  const { situation, result } = loadSituation(slug);
  return { ...situation, rules: [], result, diagram };
}
