/**
 * Input: `spec/situations/<slug>.json` (authored; schema in spec/situations/README.md) and
 * `spec/situations/expected/<slug>.json` (written by the Lean reference, never by hand).
 *
 * - The authored file becomes a `Situation`: slug = file name; `replay` defaults to true;
 *   `notReplayed` is required exactly when `replay` is false; steps get `branch` 0, `timeout`
 *   false, `text` null; the net gets `priority` 0, `timing` null, `output` null and empty arc
 *   and property lists by default; markings keep counts above zero, keys sorted. `title`, `text`
 *   and `group` are required by the site; a missing one, an unknown group or an unknown key
 *   fails the build.
 * - Every `replay: true` situation has an expected file: `fired: true` / `blocked: true`
 *   become `kind`, a missing `timeout` is false, a missing `arc.n` null. The result is checked
 *   with `replayResult` from `decode-site.ts` and against the authored steps (same transitions,
 *   branches and outcomes, in order, stopping at the first blocked step). An expected file
 *   without a `replay: true` situation fails the build.
 * - Sorted by slug (the site re-sorts by group).
 */
import { readdirSync } from 'node:fs';
import { arr, bool, DecodeError, int, lit, nullable, num, oneOf, str } from '../../decode.js';
import { outputSpec as outputSpecDecoder, replayResult as replayResultDecoder } from '../../decode-site.js';
import type {
  CorpusNet,
  InputArc,
  Marking,
  NetProperty,
  NetTransition,
  NotReplayed,
  ReplayResult,
  ReplayStep,
  Situation,
  SituationGroup,
  SituationStep,
  Timing,
} from '../../model.js';
import { NOT_REPLAYED, SITUATION_GROUPS, STEP_EXPECTS } from '../../model.js';
import { repoPath } from '../paths.js';
import { decodeFile, objWith, parseJson } from './json-input.js';
import { readSource } from './source.js';
import { byString } from './text.js';

export const SITUATIONS_DIR = 'spec/situations';
export const EXPECTED_DIR = 'spec/situations/expected';
const SLUG_RE = /^[a-z0-9]+(?:-[a-z0-9]+)*$/;

export interface SituationInput {
  readonly situation: Situation;
  /** Null exactly when `situation.replay` is false. */
  readonly result: ReplayResult | null;
}

// ---------------------------------------------------------------------------------------------
// Raw shapes
// ---------------------------------------------------------------------------------------------

const rawMarking = (v: unknown, p: string): Readonly<Record<string, number>> => {
  // A DecodeError, so decodeFile prefixes the file name as it does for every other key.
  if (typeof v !== 'object' || v === null || Array.isArray(v)) throw new DecodeError(p, 'expected an object of token counts');
  const out: Record<string, number> = {};
  for (const [place, count] of Object.entries(v)) out[place] = int(count, `${p}.${place}`);
  return out;
};

const rawInput = objWith({ place: str, kind: str }, { n: int });
const rawTiming = objWith({ kind: str }, { earliestMs: num, latestMs: num });
const rawTransition = objWith(
  { name: str },
  {
    inputs: arr(rawInput),
    inhibitors: arr(str),
    reads: arr(str),
    resets: arr(str),
    output: nullable(outputSpecDecoder),
    priority: int,
    timing: rawTiming,
  },
);
const rawProperty = objWith(
  { id: str, type: str },
  { sinks: arr(str), place: str, bound: int, places: arr(str), min: int, max: int },
);
const rawStep = objWith({ fire: str }, { branch: int, timeout: bool, text: str, expect: oneOf(STEP_EXPECTS) });
const rawSituation = objWith(
  { title: str, text: str, group: str, places: arr(str), marking: rawMarking, transitions: arr(rawTransition) },
  { cites: arr(str), replay: bool, notReplayed: str, steps: arr(rawStep), id: str, properties: arr(rawProperty) },
);

const rawReason = objWith(
  { kind: str },
  { place: str, arc: objWith({ kind: str }, { n: int }), need: int, have: int, count: int, branch: int, timeout: bool },
);
const rawReplayStep = objWith(
  { index: int, fire: str, branch: int },
  { timeout: bool, fired: lit(true), blocked: lit(true), marking: rawMarking, reason: rawReason, requirement: str, message: str },
);
const rawExpected = objWith({ slug: str, reference: str, initial: rawMarking, complete: bool, steps: arr(rawReplayStep) }, {});

// ---------------------------------------------------------------------------------------------
// Normalising
// ---------------------------------------------------------------------------------------------

/** Counts above zero, keys sorted; a negative count is an error. */
export function normalMarking(m: Readonly<Record<string, number>>, where: string): Marking {
  const out: Record<string, number> = {};
  for (const place of Object.keys(m).sort(byString)) {
    const n = m[place] ?? 0;
    if (n < 0) throw new Error(`${where}: ${place} has ${n} tokens`);
    if (n > 0) out[place] = n;
  }
  return out;
}

function inputArc(a: DecodedInput, where: string): InputArc {
  switch (a.kind) {
    case 'one':
    case 'all':
      if (a.n !== undefined) throw new Error(`${where}: a "${a.kind}" arc takes no n`);
      return { kind: a.kind, place: a.place };
    case 'exactly':
    case 'atLeast':
      if (a.n === undefined || a.n < 1) throw new Error(`${where}: an "${a.kind}" arc needs n >= 1`);
      return { kind: a.kind, place: a.place, n: a.n };
    default:
      throw new Error(`${where}: unknown input kind "${a.kind}"`);
  }
}
type DecodedInput = ReturnType<typeof rawInput>;

const TIMING_KINDS = ['immediate', 'unconstrained', 'deadline', 'delayed', 'window', 'exact'] as const;

function timing(t: ReturnType<typeof rawTiming>, where: string): Timing {
  const kind = TIMING_KINDS.find((k) => k === t.kind);
  if (kind === undefined) throw new Error(`${where}: unknown timing kind "${t.kind}"`);
  return { kind, earliestMs: t.earliestMs ?? null, latestMs: t.latestMs ?? null };
}

function transition(t: ReturnType<typeof rawTransition>, where: string): NetTransition {
  return {
    name: t.name,
    inputs: (t.inputs ?? []).map((a, i) => inputArc(a, `${where}.inputs[${i}]`)),
    inhibitors: t.inhibitors ?? [],
    reads: t.reads ?? [],
    resets: t.resets ?? [],
    output: t.output ?? null,
    priority: t.priority ?? 0,
    timing: t.timing === undefined ? null : timing(t.timing, `${where}.timing`),
  };
}

function property(p: ReturnType<typeof rawProperty>, where: string): NetProperty {
  const need = <T>(value: T | undefined, key: string): T => {
    if (value === undefined) throw new Error(`${where}: a "${p.type}" property needs "${key}"`);
    return value;
  };
  switch (p.type) {
    case 'deadlock-free':
    case 'terminates-at-sink':
      return { type: p.type, id: p.id, sinks: need(p.sinks, 'sinks') };
    case 'place-bound':
      return { type: p.type, id: p.id, place: need(p.place, 'place'), bound: need(p.bound, 'bound') };
    case 'mutual-exclusion':
    case 'unreachable':
      return { type: p.type, id: p.id, places: need(p.places, 'places') };
    case 'quiescent-count':
      return { type: p.type, id: p.id, places: need(p.places, 'places'), min: need(p.min, 'min'), max: p.max ?? null };
    default:
      throw new Error(`${where}: unknown property type "${p.type}"`);
  }
}

export function parseSituation(slug: string, text: string, file: string): Situation {
  if (!SLUG_RE.test(slug)) throw new Error(`${file}: the file name must be lowercase words joined by "-"`);
  const raw = decodeFile(rawSituation, parseJson(text, file), file);
  const group = SITUATION_GROUPS.find((g): g is SituationGroup => g === raw.group);
  if (group === undefined) throw new Error(`${file}: group "${raw.group}" is not one of ${SITUATION_GROUPS.join(', ')}`);
  const replay = raw.replay ?? true;
  let notReplayed: NotReplayed | null = null;
  if (replay) {
    if (raw.notReplayed !== undefined) throw new Error(`${file}: "notReplayed" belongs only in a "replay": false file`);
    if (raw.steps === undefined || raw.steps.length === 0) throw new Error(`${file}: a replayed situation needs steps`);
  } else {
    notReplayed = NOT_REPLAYED.find((r) => r === raw.notReplayed) ?? null;
    if (notReplayed === null) throw new Error(`${file}: a "replay": false file needs "notReplayed", one of ${NOT_REPLAYED.join(', ')}`);
  }
  if (raw.title.trim() === '' || raw.text.trim() === '') throw new Error(`${file}: title and text must not be empty`);
  const names = raw.transitions.map((t) => t.name);
  const twice = names.find((n, i) => names.indexOf(n) !== i);
  if (twice !== undefined) throw new Error(`${file}: two transitions are named "${twice}"`);

  const net: CorpusNet = {
    places: raw.places,
    marking: normalMarking(raw.marking, `${file}: $.marking`),
    transitions: raw.transitions.map((t, i) => transition(t, `${file}: $.transitions[${i}]`)),
    properties: (raw.properties ?? []).map((p, i) => property(p, `${file}: $.properties[${i}]`)),
  };
  const steps = (raw.steps ?? []).map(
    (s): SituationStep => ({ fire: s.fire, branch: s.branch ?? 0, timeout: s.timeout ?? false, text: s.text ?? null, expect: s.expect ?? 'fired' }),
  );
  const blockedAt = steps.findIndex((s) => s.expect === 'blocked');
  if (blockedAt >= 0 && blockedAt !== steps.length - 1) {
    throw new Error(`${file}: step ${blockedAt + 1} expects "blocked", but a blocked step must be the last one (the replay stops there)`);
  }
  return { slug, title: raw.title, text: raw.text, group, cites: raw.cites ?? [], replay, notReplayed, net, steps };
}

function blockReason(r: ReturnType<typeof rawReason>): unknown {
  switch (r.kind) {
    case 'inputShort':
      return { kind: r.kind, place: r.place, arc: r.arc === undefined ? undefined : { kind: r.arc.kind, n: r.arc.n ?? null }, need: r.need, have: r.have };
    case 'inhibitorMarked':
      return { kind: r.kind, place: r.place, count: r.count };
    case 'readEmpty':
      return { kind: r.kind, place: r.place };
    case 'noSuchBranch':
      return { kind: r.kind, branch: r.branch, timeout: r.timeout ?? false };
    default:
      return { kind: r.kind };
  }
}

/** Maps the expected file to the model shape, then checks it with the site decoder. */
export function parseReplay(text: string, file: string): ReplayResult {
  const raw = decodeFile(rawExpected, parseJson(text, file), file);
  const steps = raw.steps.map((s): unknown => {
    const base = { index: s.index, fire: s.fire, branch: s.branch, timeout: s.timeout ?? false };
    if (s.fired === true && s.blocked === undefined) return { kind: 'fired', ...base, marking: s.marking };
    if (s.blocked === true && s.fired === undefined) {
      return { kind: 'blocked', ...base, reason: s.reason === undefined ? undefined : blockReason(s.reason), requirement: s.requirement, message: s.message };
    }
    return { kind: 'neither fired nor blocked', ...base };
  });
  const shaped = { slug: raw.slug, reference: raw.reference, initial: raw.initial, complete: raw.complete, steps };
  const result = decodeFile(replayResultDecoder, shaped, file);
  return {
    ...result,
    initial: normalMarking(result.initial, `${file}: $.initial`),
    steps: result.steps.map((s): ReplayStep => (s.kind === 'fired' ? { ...s, marking: normalMarking(s.marking, `${file}: $.steps[${s.index}].marking`) } : s)),
  };
}

/**
 * The replay must follow the authored steps, stop at its first blocked step, and give every step
 * the outcome its author expects (`expect`, default `fired`). The last check is what lets the
 * page say "Lean replay agrees": without it any replay would agree.
 */
export function checkReplay(situation: Situation, result: ReplayResult, file: string): void {
  const fail = (message: string): Error => new Error(`${file}: ${message}; regenerate with python3 scripts/situations.py --update`);
  const situationFile = `${SITUATIONS_DIR}/${situation.slug}.json`;
  if (result.slug !== situation.slug) throw fail(`slug "${result.slug}" is not "${situation.slug}"`);
  if (result.steps.length > situation.steps.length) throw fail('more replayed steps than authored steps');
  for (const [k, step] of result.steps.entries()) {
    const authored = situation.steps[k];
    if (authored === undefined || step.index !== k) throw fail(`step ${k} has index ${step.index}`);
    if (step.fire !== authored.fire || step.branch !== authored.branch || step.timeout !== authored.timeout) {
      throw fail(`step ${k} replays ${step.fire} (branch ${step.branch}${step.timeout ? ', timeout' : ''}), the situation fires ${authored.fire}`);
    }
    if (step.kind === 'blocked' && k !== result.steps.length - 1) throw fail(`step ${k} is blocked but the replay goes on`);
    if (step.kind !== authored.expect) {
      const why = step.kind === 'blocked' ? ` (${step.message})` : '';
      throw new Error(`${situationFile}: step ${k + 1} (${authored.fire}) expects "${authored.expect}", but the Lean replay says "${step.kind}"${why}. `
        + 'Fix the net or the steps, or set "expect" on the step.');
    }
  }
  if (result.steps.length < situation.steps.length && result.steps[result.steps.length - 1]?.kind === 'blocked') {
    throw new Error(`${situationFile}: the Lean replay stops at a blocked step ${result.steps.length}, but the situation has ${situation.steps.length} steps.`);
  }
  const fired = result.steps.every((s) => s.kind === 'fired');
  const complete = fired && result.steps.length === situation.steps.length;
  if (result.complete !== complete) throw fail(`"complete" is ${result.complete}, the steps say ${complete}`);
  if (!complete && fired) throw fail('the replay stops before the last step without a blocked step');
  if (JSON.stringify(result.initial) !== JSON.stringify(situation.net.marking)) throw fail('"initial" is not the situation\'s marking');
}

function jsonFiles(root: string, dir: string): string[] {
  return readdirSync(repoPath(root, dir), { withFileTypes: true })
    .filter((e) => e.isFile() && e.name.endsWith('.json'))
    .map((e) => e.name.slice(0, -'.json'.length))
    .sort(byString);
}

export function readSituations(root: string): readonly SituationInput[] {
  const slugs = jsonFiles(root, SITUATIONS_DIR);
  let expected: string[] = [];
  try {
    expected = jsonFiles(root, EXPECTED_DIR);
  } catch {
    expected = [];
  }
  const out = slugs.map((slug): SituationInput => {
    const file = `${SITUATIONS_DIR}/${slug}.json`;
    const situation = parseSituation(slug, readSource(root, file), file);
    const expectedFile = `${EXPECTED_DIR}/${slug}.json`;
    const hasExpected = expected.includes(slug);
    if (!situation.replay) {
      if (hasExpected) throw new Error(`${expectedFile}: ${file} says "replay": false; delete the stale expected file`);
      return { situation, result: null };
    }
    if (!hasExpected) throw new Error(`${file}: no ${expectedFile}; run python3 scripts/situations.py --update`);
    const result = parseReplay(readSource(root, expectedFile), expectedFile);
    checkReplay(situation, result, expectedFile);
    return { situation, result };
  });
  for (const slug of expected) {
    if (!slugs.includes(slug)) throw new Error(`${EXPECTED_DIR}/${slug}.json: no ${SITUATIONS_DIR}/${slug}.json`);
  }
  return out;
}
