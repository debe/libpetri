/**
 * The reference firing rule of the conformance corpus, written in test code straight from the
 * spec ([CORE-022], [CORE-030]–[CORE-036], [IO-001]–[IO-004], [IO-013]–[IO-016]) and sharing nothing with
 * the verifier: it replays a language's counterexample and decides each property's bad-state
 * predicate ([VER-002]). The conformance check itself is a pure function of a verdict, its trace
 * and the reference's expected entry, so it can be exercised on fabricated results.
 */
import { reapable, type InputSpec, type NetSpec, type OutputSpec, type PropertySpec, type TransitionSpec } from './loader.js';

/** A marking: place name -> token count; an absent name holds none. */
export type Marking = ReadonlyMap<string, number>;

const count = (m: Marking, p: string): number => m.get(p) ?? 0;

function required(i: InputSpec): number {
  switch (i.kind) {
    case 'one': return 1;
    case 'exactly': return i.n;
    case 'all': return 1;
    case 'atLeast': return i.n;
  }
}

/** [CORE-022]: inputs hold their required count, reads are marked, inhibitors are empty. */
export function enabled(t: TransitionSpec, m: Marking): boolean {
  return t.inputs.every(i => count(m, i.place) >= required(i))
    && t.reads.every(p => count(m, p) >= 1)
    && t.inhibitors.every(p => count(m, p) === 0);
}

/** One deposit leaf: one token into a place, or a forward's consumed multiplicity of `from`. */
type Leaf = { readonly place: string } | { readonly from: string; readonly to: string };

/**
 * The claims an action that COMPLETES can write ([IO-015], [IO-016]): `and` is a product, `xor`
 * a union, a `timeout` claims its child's claim, and a `forward` claims its `to` place with ONE
 * token, as a `place` does.
 */
function completions(o: OutputSpec): Leaf[][] {
  switch (o.type) {
    case 'place': return [[{ place: o.place }]];
    case 'forward': return [[{ place: o.to }]];
    case 'timeout': return completions(o.child);
    case 'xor': return o.children.flatMap(completions);
    case 'and': {
      let acc: Leaf[][] = [[]];
      for (const c of o.children) {
        const alts = completions(c);
        acc = acc.flatMap(a => alts.map(b => [...a, ...b]));
      }
      return acc;
    }
  }
}

/**
 * What the marking receives when a timeout's budget expires ([IO-013] AC5): its child's
 * alternatives and nothing else, a `forward` depositing one token per token the firing
 * consumed from `from` ([IO-014]).
 */
function timeoutOutcome(o: OutputSpec): Leaf[][] {
  switch (o.type) {
    case 'place': return [[{ place: o.place }]];
    case 'forward': return [[{ from: o.from, to: o.to }]];
    case 'timeout': return timeoutOutcome(o.child);
    case 'xor': return o.children.flatMap(timeoutOutcome);
    case 'and': {
      let acc: Leaf[][] = [[]];
      for (const c of o.children) {
        const alts = timeoutOutcome(c);
        acc = acc.flatMap(a => alts.map(b => [...a, ...b]));
      }
      return acc;
    }
  }
}

/** One timeout outcome per `timeout` node anywhere in the tree. */
function timeoutOutcomes(o: OutputSpec): Leaf[][] {
  switch (o.type) {
    case 'place':
    case 'forward': return [];
    case 'timeout': return [...timeoutOutcome(o.child), ...timeoutOutcomes(o.child)];
    case 'xor':
    case 'and': return o.children.flatMap(timeoutOutcomes);
  }
}

/**
 * The markings one firing of `t` can produce: consume ([IO-007]: `all` / `atLeast` drain the
 * place), clear the reset places ([CORE-034]), then deposit either a completion claim of the
 * output tree or the outcome of one of its timeouts.
 */
export function fire(t: TransitionSpec, m: Marking): Marking[] {
  const base = new Map(m);
  const consumed = new Map<string, number>();
  for (const i of t.inputs) {
    const have = count(base, i.place);
    const n = i.kind === 'one' ? 1 : i.kind === 'exactly' ? i.n : have;
    base.set(i.place, have - n);
    consumed.set(i.place, n);
  }
  for (const p of t.resets) base.set(p, 0);
  const alts = t.output === null ? [[]] : [...completions(t.output), ...timeoutOutcomes(t.output)];
  return alts.map(alt => {
    const next = new Map(base);
    for (const leaf of alt) {
      if ('place' in leaf) next.set(leaf.place, count(next, leaf.place) + 1);
      else next.set(leaf.to, count(next, leaf.to) + (consumed.get(leaf.from) ?? 0));
    }
    return next;
  });
}

/** Reap-quiescent ([VER-002], [TIME-013]): every enabled transition is reapable. */
export function quiescent(net: NetSpec, m: Marking): boolean {
  return !net.transitions.some(t => !reapable(t) && enabled(t, m));
}

/** The property's bad-state predicate ([VER-002]). */
export function bad(net: NetSpec, prop: PropertySpec, m: Marking): boolean {
  switch (prop.type) {
    case 'deadlock-free':
      return quiescent(net, m) && [...m].some(([p, n]) => n > 0 && !prop.sinks.includes(p));
    case 'terminates-at-sink':
      return quiescent(net, m) && !prop.sinks.some(s => count(m, s) > 0);
    case 'place-bound':
      return count(m, prop.place) > prop.bound;
    case 'mutual-exclusion':
      // Pairwise ([VER-002]): two entries of the list marked at once.
      return prop.places.filter(p => count(m, p) > 0).length >= 2;
    case 'unreachable':
      return prop.places.every(p => count(m, p) > 0);
    case 'quiescent-count': {
      if (!quiescent(net, m)) return false;
      const sum = [...new Set(prop.places)].reduce((s, p) => s + count(m, p), 0);
      return sum < prop.min || (prop.max !== undefined && sum > prop.max);
    }
  }
}

export function initialMarking(net: NetSpec): Marking {
  return new Map(net.marking);
}

/**
 * A trace name with a flattener branch suffix (`t_b1`) stripped — only when the stripped name
 * is a transition of the net and the full name is not.
 */
export function stripBranch(net: NetSpec, name: string): string {
  const m = /^(.*)_b\d+$/.exec(name);
  if (!m) return name;
  const names = new Set(net.transitions.map(t => t.name));
  return names.has(m[1]!) && !names.has(name) ? m[1]! : name;
}

const key = (m: Marking): string =>
  [...m].filter(([, n]) => n > 0).sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0)).map(([p, n]) => `${p}:${n}`).join(',');

/**
 * Replays a trace under the reference firing rule, keeping the set of states the output
 * alternatives allow. Returns `null` when some final state is bad, else why not.
 */
export function replay(net: NetSpec, prop: PropertySpec, trace: readonly string[]): string | null {
  let states: Marking[] = [initialMarking(net)];
  for (const [step, raw] of trace.entries()) {
    const name = stripBranch(net, raw);
    const t = net.transitions.find(x => x.name === name);
    if (!t) return `step ${step}: unknown transition '${raw}'`;
    const next = new Map<string, Marking>();
    for (const s of states) {
      if (!enabled(t, s)) continue;
      for (const n of fire(t, s)) next.set(key(n), n);
    }
    if (next.size === 0) return `step ${step}: '${raw}' not enabled in {${states.map(key).join(' | ')}}`;
    states = [...next.values()];
  }
  return states.some(s => bad(net, prop, s))
    ? null
    : `final state(s) {${states.map(key).join(' | ')}} do not violate ${prop.id} (${prop.type})`;
}

// ======================================================================
// The conformance rule
// ======================================================================

export type RefVerdict = 'proven' | 'violated' | 'unknown';

export interface ExpectedEntry {
  readonly property: string;
  readonly verdict: RefVerdict;
  readonly trace?: readonly string[];
  readonly reason?: string;
}

export interface LangResult {
  readonly verdict: 'proven' | 'violated' | 'unknown';
  readonly trace: readonly string[];
  /**
   * Whether a `violated` carries a firing sequence (possibly `[]`, the initial marking). An
   * untraced violation is a rule-3 finding (README clarification 6).
   */
  readonly traced: boolean;
  readonly reason?: string;
  /**
   * Whether the verdict is of a net the in-flight split rewrote ([VER-004]): its trace names
   * completion steps the reference does not have, so it is not replayed. Default pass only.
   */
  readonly split?: boolean;
  /** The abstract replay's confirmation of a `violated` trace (`counterexampleConfirmed`). */
  readonly confirmed?: boolean | null;
}

export interface Finding {
  readonly kind:
    | 'WRONG PROVEN' | 'WRONG VIOLATED' | 'FALSIFIES REFERENCE' | 'REPLAY FAILS' | 'UNTRACED VIOLATED'
    | 'STALE EXPECTED';
  readonly net: string;
  readonly property: string;
  readonly route: string;
  readonly detail: string;
}

/**
 * The README conformance rule for one (net, property, route). `expected` undefined counts as a
 * reference `unknown` here; the corpus runner reports such a property as stale before calling.
 */
export function checkConformance(
  net: NetSpec,
  prop: PropertySpec,
  route: string,
  result: LangResult,
  expected: ExpectedEntry | undefined,
): Finding[] {
  const ref: RefVerdict = expected?.verdict ?? 'unknown';
  const f = (kind: Finding['kind'], detail: string): Finding => ({ kind, net: net.id, property: prop.id, route, detail });
  if (result.verdict === 'proven') {
    return ref === 'violated'
      ? [f('WRONG PROVEN', `the reference violates it via [${(expected?.trace ?? []).join(', ')}]`)]
      : [];
  }
  if (result.verdict !== 'violated') return [];
  if (!result.traced) {
    // Rule 3: a violation must come with a firing sequence the reference can replay — `[]`
    // when the initial marking violates (README clarification 6).
    return ref === 'proven'
      ? [f('WRONG VIOLATED', 'the reference proves it; the violation carries no firing sequence')]
      : [f('UNTRACED VIOLATED', 'no firing sequence to replay; an initial-marking violation must '
        + 'report the empty trace')];
  }
  const why = replay(net, prop, result.trace);
  const trace = `[${result.trace.join(', ')}]`;
  if (ref === 'proven') {
    return why === null
      ? [f('FALSIFIES REFERENCE', `trace ${trace} replays under the reference firing rule and falsifies the reference's proof`)]
      : [f('WRONG VIOLATED', `the reference proves it; trace ${trace} does not replay: ${why}`)];
  }
  return why === null ? [] : [f('REPLAY FAILS', `trace ${trace} does not replay: ${why}`)];
}

/**
 * The default pass ([VER-004] split on) is held to rules 1, 3 and 4 only: the split adds the
 * executor's runs with an action in flight, which the atomic reference does not have, so a
 * `violated` where the reference proves the property is allowed (rule 2 is skipped and counted
 * by the caller). A trace of a split net names completion steps and is not replayed.
 */
export function checkDefaultPassConformance(
  net: NetSpec,
  prop: PropertySpec,
  route: string,
  result: LangResult,
  expected: ExpectedEntry | undefined,
): Finding[] {
  const ref: RefVerdict = expected?.verdict ?? 'unknown';
  const f = (kind: Finding['kind'], detail: string): Finding => ({ kind, net: net.id, property: prop.id, route, detail });
  if (result.verdict === 'proven') {
    return ref === 'violated'
      ? [f('WRONG PROVEN', `the reference violates it via [${(expected?.trace ?? []).join(', ')}]`)]
      : [];
  }
  if (result.verdict !== 'violated') return [];
  if (!result.traced) {
    return [f('UNTRACED VIOLATED', 'no firing sequence to replay; an initial-marking violation must '
      + 'report the empty trace')];
  }
  if (result.split === true) return [];
  const why = replay(net, prop, result.trace);
  return why === null ? [] : [f('REPLAY FAILS', `trace [${result.trace.join(', ')}] does not replay: ${why}`)];
}

export function renderFinding(x: Finding): string {
  return `${x.kind} [${x.net} ${x.property} @${x.route}]: ${x.detail}`;
}
