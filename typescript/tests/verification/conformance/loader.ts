/**
 * Loader for the cross-language conformance corpus (`spec/verification-fixtures/conformance/`).
 *
 * Parses a net file exactly per the schema in the corpus README into two things: the raw
 * {@link NetSpec} (what the independent reference firing rule in `reference.ts` reads) and
 * the real libpetri objects built with the public builder API (net, initial marking,
 * properties with their sinks) that the verifier runs on.
 */
import { PetriNet } from '../../../src/core/petri-net.js';
import { Transition } from '../../../src/core/transition.js';
import { place, type Place } from '../../../src/core/place.js';
import { all, atLeast, exactly, one, type In } from '../../../src/core/in.js';
import { and, forwardInput, outPlace, timeout, xor, type Out } from '../../../src/core/out.js';
import type { TransitionAction } from '../../../src/core/transition-action.js';
import { deadline, delayed, exact, immediate, window, type Timing } from '../../../src/core/timing.js';
import { MarkingState } from '../../../src/verification/marking-state.js';
import {
  deadlockFree,
  mutualExclusion,
  placeBound,
  quiescentCount,
  terminatesAtSink,
  unreachable,
  type SmtProperty,
} from '../../../src/verification/smt-property.js';

// ======================================================================
// Schema
// ======================================================================

export type InputSpec =
  | { readonly place: string; readonly kind: 'one' }
  | { readonly place: string; readonly kind: 'exactly'; readonly n: number }
  | { readonly place: string; readonly kind: 'all' }
  | { readonly place: string; readonly kind: 'atLeast'; readonly n: number };

export type OutputSpec =
  | { readonly type: 'place'; readonly place: string }
  | { readonly type: 'and'; readonly children: readonly OutputSpec[] }
  | { readonly type: 'xor'; readonly children: readonly OutputSpec[] }
  | { readonly type: 'timeout'; readonly afterMs: number; readonly child: OutputSpec }
  | { readonly type: 'forward'; readonly from: string; readonly to: string };

export interface TransitionSpec {
  readonly name: string;
  readonly inputs: readonly InputSpec[];
  readonly inhibitors: readonly string[];
  readonly reads: readonly string[];
  readonly resets: readonly string[];
  readonly output: OutputSpec | null;
  readonly priority: number;
  /** The schema's `timing` ([TIME-002]..[TIME-006]); absent = immediate. */
  readonly timing?: TimingSpec;
}

export interface TimingSpec {
  readonly kind: 'immediate' | 'unconstrained' | 'deadline' | 'delayed' | 'window' | 'exact';
  readonly earliestMs?: number;
  readonly latestMs?: number;
}

/** Reapable ([TIME-013]): `deadline` or `window` timing. */
export function reapable(t: TransitionSpec): boolean {
  return t.timing?.kind === 'deadline' || t.timing?.kind === 'window';
}

export type PropertySpec =
  | { readonly id: string; readonly type: 'deadlock-free'; readonly sinks: readonly string[] }
  | { readonly id: string; readonly type: 'terminates-at-sink'; readonly sinks: readonly string[] }
  | { readonly id: string; readonly type: 'place-bound'; readonly place: string; readonly bound: number }
  | { readonly id: string; readonly type: 'mutual-exclusion'; readonly places: readonly string[] }
  | { readonly id: string; readonly type: 'unreachable'; readonly places: readonly string[] }
  | {
      readonly id: string;
      readonly type: 'quiescent-count';
      readonly places: readonly string[];
      readonly min: number;
      readonly max: number | undefined;
    };

export interface NetSpec {
  readonly id: string;
  readonly places: readonly string[];
  readonly marking: ReadonlyMap<string, number>;
  readonly transitions: readonly TransitionSpec[];
  readonly properties: readonly PropertySpec[];
}

/** A property ready for the verifier: the libpetri property plus its sink places. */
export interface LoadedProperty {
  readonly spec: PropertySpec;
  readonly property: SmtProperty;
  readonly sinks: readonly Place<unknown>[];
}

export interface LoadedNet {
  readonly spec: NetSpec;
  readonly net: PetriNet;
  readonly initialMarking: MarkingState;
  readonly properties: readonly LoadedProperty[];
  /**
   * Mutual exclusions over three or more places: pairwise in the spec ([VER-002]), but
   * TypeScript's `mutualExclusion` takes exactly two, so the runner skips and counts them
   * (README clarification 1). Never run.
   */
  readonly skipped: readonly PropertySpec[];
}

/** Raised when a file uses a shape this language's API cannot express. */
export class SchemaNotExpressible extends Error {}

// ======================================================================
// Parsing (strict: unknown kinds / types throw)
// ======================================================================

function fail(id: string, msg: string): never {
  throw new Error(`conformance net '${id}': ${msg}`);
}

function str(id: string, v: unknown, what: string): string {
  if (typeof v !== 'string') fail(id, `${what} must be a string, got ${JSON.stringify(v)}`);
  return v;
}

function nat(id: string, v: unknown, what: string, min = 0): number {
  if (typeof v !== 'number' || !Number.isInteger(v) || v < min) {
    fail(id, `${what} must be an integer >= ${min}, got ${JSON.stringify(v)}`);
  }
  return v;
}

function strings(id: string, v: unknown, what: string): string[] {
  if (v === undefined || v === null) return [];
  if (!Array.isArray(v)) fail(id, `${what} must be an array`);
  return v.map((x, i) => str(id, x, `${what}[${i}]`));
}

function parseInput(id: string, raw: any): InputSpec {
  const p = str(id, raw?.place, 'input place');
  switch (raw?.kind) {
    case 'one': return { place: p, kind: 'one' };
    case 'all': return { place: p, kind: 'all' };
    case 'exactly': return { place: p, kind: 'exactly', n: nat(id, raw.n, `exactly(${p}).n`, 1) };
    case 'atLeast': return { place: p, kind: 'atLeast', n: nat(id, raw.n, `atLeast(${p}).n`, 1) };
    default: return fail(id, `unknown input kind ${JSON.stringify(raw?.kind)}`);
  }
}

function parseOutput(id: string, raw: any): OutputSpec {
  switch (raw?.type) {
    case 'place': return { type: 'place', place: str(id, raw.place, 'output place') };
    case 'and':
    case 'xor': {
      if (!Array.isArray(raw.children)) fail(id, `${raw.type} needs children`);
      return { type: raw.type, children: raw.children.map((c: unknown) => parseOutput(id, c)) };
    }
    case 'timeout':
      return { type: 'timeout', afterMs: nat(id, raw.afterMs, 'timeout.afterMs'), child: parseOutput(id, raw.child) };
    case 'forward':
      return { type: 'forward', from: str(id, raw.from, 'forward.from'), to: str(id, raw.to, 'forward.to') };
    default:
      return fail(id, `unknown output type ${JSON.stringify(raw?.type)}`);
  }
}

function parseProperty(id: string, raw: any): PropertySpec {
  const pid = str(id, raw?.id, 'property id');
  switch (raw?.type) {
    case 'deadlock-free':
    case 'terminates-at-sink':
      return { id: pid, type: raw.type, sinks: strings(id, raw.sinks, `${pid}.sinks`) };
    case 'place-bound':
      return { id: pid, type: 'place-bound', place: str(id, raw.place, `${pid}.place`), bound: nat(id, raw.bound, `${pid}.bound`) };
    case 'mutual-exclusion':
      return { id: pid, type: 'mutual-exclusion', places: strings(id, raw.places, `${pid}.places`) };
    case 'unreachable':
      return { id: pid, type: 'unreachable', places: strings(id, raw.places, `${pid}.places`) };
    case 'quiescent-count':
      return {
        id: pid,
        type: 'quiescent-count',
        places: strings(id, raw.places, `${pid}.places`),
        min: nat(id, raw.min, `${pid}.min`),
        max: raw.max === undefined || raw.max === null ? undefined : nat(id, raw.max, `${pid}.max`),
      };
    default:
      return fail(id, `unknown property type ${JSON.stringify(raw?.type)}`);
  }
}

function parseTiming(id: string, name: string, raw: any): TimingSpec {
  const kind = str(id, raw?.kind, `${name}.timing.kind`);
  const ms = (k: 'earliestMs' | 'latestMs'): number => nat(id, raw[k], `${name}.timing.${k}`);
  switch (kind) {
    case 'immediate':
    case 'unconstrained':
      return { kind };
    case 'deadline':
      return { kind, latestMs: ms('latestMs') };
    case 'delayed':
      return { kind, earliestMs: ms('earliestMs') };
    case 'window':
      return { kind, earliestMs: ms('earliestMs'), latestMs: ms('latestMs') };
    case 'exact':
      return { kind, earliestMs: ms('earliestMs') };
    default:
      return fail(id, `${name}: unknown timing kind '${kind}'`);
  }
}

function toTiming(t: TimingSpec): Timing {
  switch (t.kind) {
    case 'immediate':
    case 'unconstrained': return immediate();
    case 'deadline': return deadline(t.latestMs!);
    case 'delayed': return delayed(t.earliestMs!);
    case 'window': return window(t.earliestMs!, t.latestMs!);
    case 'exact': return exact(t.earliestMs!);
  }
}

/** Parses a net file's JSON value into a {@link NetSpec}. */
export function parseNet(raw: any): NetSpec {
  const id = str('?', raw?.id, 'id');
  const marking = new Map<string, number>();
  for (const [name, n] of Object.entries(raw.marking ?? {})) {
    marking.set(name, nat(id, n, `marking.${name}`));
  }
  if (!Array.isArray(raw.transitions)) fail(id, 'transitions must be an array');
  const transitions: TransitionSpec[] = raw.transitions.map((t: any): TransitionSpec => {
    const name = str(id, t?.name, 'transition name');
    const inputs = (t.inputs ?? []).map((i: unknown) => parseInput(id, i));
    const seen = new Set<string>();
    for (const i of inputs) {
      if (seen.has(i.place)) fail(id, `${name}: two input arcs on '${i.place}' (CORE-030)`);
      seen.add(i.place);
    }
    return {
      name,
      inputs,
      inhibitors: strings(id, t.inhibitors, `${name}.inhibitors`),
      reads: strings(id, t.reads, `${name}.reads`),
      resets: strings(id, t.resets, `${name}.resets`),
      output: t.output === undefined || t.output === null ? null : parseOutput(id, t.output),
      priority: t.priority === undefined || t.priority === null ? 0 : (t.priority as number),
      ...(t.timing === undefined || t.timing === null ? {} : { timing: parseTiming(id, name, t.timing) }),
    };
  });
  return {
    id,
    places: strings(id, raw.places, 'places'),
    marking,
    transitions,
    properties: (raw.properties ?? []).map((p: unknown) => parseProperty(id, p)),
  };
}

// ======================================================================
// Building the real net
// ======================================================================

/**
 * The action every loaded transition carries: the verifier reads structure only
 * ([CORE-043] rejects `passthrough()` on an output-declaring transition), and this one
 * fails loudly if a corpus net is ever executed.
 */
const STRUCTURE_ONLY: TransitionAction = async () => {
  throw new Error('conformance net: structure only, never executed');
};

/** Loads a parsed spec into a real net, marking and properties. */
export function buildNet(spec: NetSpec): LoadedNet {
  const places = new Map<string, Place<unknown>>();
  const p = (name: string): Place<unknown> => {
    let found = places.get(name);
    if (!found) {
      found = place<unknown>(name);
      places.set(name, found);
    }
    return found;
  };
  const toIn = (i: InputSpec): In => {
    switch (i.kind) {
      case 'one': return one(p(i.place));
      case 'exactly': return exactly(i.n, p(i.place));
      case 'all': return all(p(i.place));
      case 'atLeast': return atLeast(i.n, p(i.place));
    }
  };
  const toOut = (o: OutputSpec): Out => {
    switch (o.type) {
      case 'place': return outPlace(p(o.place));
      case 'and': return and(...o.children.map(toOut));
      case 'xor': return xor(...o.children.map(toOut));
      case 'timeout': return timeout(o.afterMs, toOut(o.child));
      case 'forward': return forwardInput(p(o.from), p(o.to));
    }
  };

  const nb = PetriNet.builder(spec.id);
  for (const t of spec.transitions) {
    const tb = Transition.builder(t.name).inputs(...t.inputs.map(toIn));
    for (const name of t.inhibitors) tb.inhibitor(p(name));
    for (const name of t.reads) tb.read(p(name));
    for (const name of t.resets) tb.reset(p(name));
    if (t.output !== null) tb.outputs(toOut(t.output));
    if (t.priority !== 0) tb.priority(t.priority);
    if (t.timing !== undefined) tb.timing(toTiming(t.timing));
    nb.transition(tb.action(STRUCTURE_ONLY).build());
  }
  for (const name of spec.places) nb.place(p(name));
  const net = nb.build();

  // The marking may name places no arc touches and the net does not declare: inert places
  // ([CORE-072], [VER-003]), carried by the marking alone.
  const mb = MarkingState.builder();
  for (const [name, n] of spec.marking) {
    if (n > 0) mb.tokens(p(name), n);
  }

  const beyondTwoPlaceApi = (ps: PropertySpec) => ps.type === 'mutual-exclusion' && ps.places.length > 2;
  const skipped = spec.properties.filter(beyondTwoPlaceApi);
  const properties = spec.properties.filter(ps => !beyondTwoPlaceApi(ps)).map((ps): LoadedProperty => {
    switch (ps.type) {
      case 'deadlock-free':
        return { spec: ps, property: deadlockFree(), sinks: ps.sinks.map(p) };
      case 'terminates-at-sink':
        return { spec: ps, property: terminatesAtSink(), sinks: ps.sinks.map(p) };
      case 'place-bound':
        return { spec: ps, property: placeBound(p(ps.place), ps.bound), sinks: [] };
      case 'mutual-exclusion':
        if (ps.places.length !== 2) {
          throw new SchemaNotExpressible(
            `conformance net '${spec.id}' property ${ps.id}: schema not expressible in TypeScript — ` +
              `mutualExclusion takes exactly two places, got ${ps.places.length}`,
          );
        }
        return { spec: ps, property: mutualExclusion(p(ps.places[0]!), p(ps.places[1]!)), sinks: [] };
      case 'unreachable':
        return { spec: ps, property: unreachable(new Set(ps.places.map(p))), sinks: [] };
      case 'quiescent-count':
        return {
          spec: ps,
          property: quiescentCount(ps.places.map(p), ps.min, ps.max ?? Infinity),
          sinks: [],
        };
    }
  });

  return { spec, net, initialMarking: mb.build(), properties, skipped };
}

/** Parses and builds in one step. */
export function loadNet(raw: unknown): LoadedNet {
  return buildNet(parseNet(raw));
}
