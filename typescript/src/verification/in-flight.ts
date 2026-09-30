/**
 * @module in-flight
 *
 * In-flight actions in verification ([VER-004], [EXEC-001], [EXEC-003]).
 *
 * Every route reads a firing as one atomic step. The executor does not fire that way: it
 * consumes a firing's inputs when the action starts and deposits its outputs when the action
 * completes, and other transitions fire in between. An asynchronous action leaves that gap open
 * for as long as it runs; a synchronous one until the end of its firing pass, because a drain
 * later in the same pass does not see the deposit ([EXEC-003] AC5).
 *
 * For most nets the gap changes nothing. A run with `t` in flight can be reordered so that
 * `t`'s deposit comes right after its start, as long as no step in between tests one of `t`'s
 * output places non-monotonically: the steps in between see more tokens there, and a
 * transition that only needs tokens is still enabled and does the same. An inhibitor arc, a
 * reset arc and a draining input (`all`, `atLeast`) are the non-monotone tests. A terminal place
 * ([EXEC-042]) counts as one, since it inhibits every transition.
 *
 * So a transition `t` needs the executor's two-step firing exactly when some transition tests
 * one of `t`'s output places that way. {@link splitInFlight} splits each such `t` into `t`
 * itself, with every input, read, inhibitor and reset arc, its timing, priority and match spec,
 * whose only output is the fresh place `inflight:<t>`, and `complete:<t>`, immediate, consuming
 * `inflight:<t>` and depositing `t`'s output spec. Every other transition stays atomic, so a net
 * without such a transition is not rewritten and verifies, and scripts, exactly as before.
 *
 * Two more readings test a place without an arc, and the verifier adds them to the tested places
 * (`SplitDemand`):
 *
 * - A **terminal place** stops the net without waiting for an action in flight ([EXEC-042]): the
 *   action is abandoned, its inputs consumed and its outputs never deposited. Removing tokens is
 *   harmless to every quiescence property but one: a `quiescentCount` with a lower bound, when
 *   some terminal does not waive it. For it the places the count reads and its waiver places are
 *   tested too (`quiescentCountDemand`), so every transition depositing there is split and
 *   the terminal, which inhibits `complete:<t>` as it inhibits every transition, models the
 *   abandonment.
 * - **Conflict priority** on Route B ([NU-052]) fires `L` only when no conflicting,
 *   higher-priority `H` is enabled, a test of `H`'s input and read places that more tokens can
 *   fail. Those places are tested too, and every such `H` is split as well: while `inflight:<H>`
 *   is marked, `H` pre-empts nothing, since the Java and TypeScript executors do not start `H`
 *   again while its action runs (`conflictDemand`).
 *
 * Three cases are refused rather than split: a transition to split that is a ν-join or a writer
 * into a coloured place; a `Timeout` forward of more than one token; and a name the split would
 * add that the net already uses. Mirrors Rust's `in_flight.rs` and Java's
 * `InFlight`.
 */
import { PetriNet } from '../core/petri-net.js';
import { place, type Place } from '../core/place.js';
import { Transition } from '../core/transition.js';
import { one, type In } from '../core/in.js';
import type { Out } from '../core/out.js';
import { immediate } from '../core/timing.js';
import { compareCodePoints } from '../core/internal/code-point-order.js';
import type { SmtProperty } from './smt-property.js';
import type { MarkingState } from './marking-state.js';

/** What {@link splitInFlight} did to a net. */
export type InFlight =
  /** No transition needs the two-step firing: verify the net as it is. */
  | { readonly type: 'atomic' }
  /** The rewritten net, and the names of the transitions it split, in net order. */
  | { readonly type: 'split'; readonly net: PetriNet; readonly split: readonly string[] }
  /** The net needs the two-step firing and the split cannot express it; no route may answer. */
  | { readonly type: 'refused'; readonly reason: string };

/** The in-flight place of transition `t`. */
export function inFlightPlace(t: string): string {
  return `inflight:${t}`;
}

/** The completion transition of transition `t`. */
export function completionTransition(t: string): string {
  return `complete:${t}`;
}

/**
 * Every place some transition tests non-monotonically: an inhibitor, a reset, a draining input
 * (`all`, `atLeast`), and every terminal place ([EXEC-042]).
 */
export function nonMonotonePlaces(net: PetriNet): Set<string> {
  const out = new Set<string>([...net.terminals].map(p => p.name));
  for (const t of net.transitions) {
    for (const a of t.inhibitors) out.add(a.place.name);
    for (const a of t.resets) out.add(a.place.name);
    for (const s of t.inputSpecs) if (s.type === 'all' || s.type === 'at-least') out.add(s.place.name);
  }
  return out;
}

/**
 * Whether `t` is a completion step: `complete:<x>`, whose one input is `one(inflight:<x>)`, with
 * no read or reset arc. It is itself a single deposit, so it is never split, which makes
 * {@link splitInFlight} idempotent, also after the terminal rewrite gave it an inhibitor.
 */
function isCompletion(t: Transition): boolean {
  if (!t.name.startsWith('complete:')) return false;
  const x = t.name.slice('complete:'.length);
  return t.inputSpecs.length === 1
    && t.inputSpecs[0]!.type === 'one'
    && t.inputSpecs[0]!.place.name === inFlightPlace(x)
    && t.reads.length === 0
    && t.resets.length === 0;
}

/**
 * The transitions of `net` that need the executor's two-step firing, in net order: those with an
 * output place some transition tests non-monotonically. `environment` names the transitions that
 * model the environment rather than an action of the net (the arrivals of [VER-006], the
 * environment of an open-net contract, [VER-022]); they stay atomic, and their arcs still count
 * as tests.
 */
export function inFlightTransitions(net: PetriNet, environment: ReadonlySet<string> = new Set()): string[] {
  return inFlightTransitionsFor(net, environment, emptyDemand());
}

/**
 * What a verification tests beyond the arcs of its net ({@link nonMonotonePlaces}), and so adds to
 * the split (module docs).
 * @internal
 */
export interface SplitDemand {
  /** Places tested non-monotonically: every transition depositing into one is split. */
  readonly tested: Set<string>;
  /** Transitions split whatever their outputs. */
  readonly forced: Set<string>;
}

/** @internal */
export function emptyDemand(): SplitDemand {
  return { tested: new Set(), forced: new Set() };
}

/** @internal `a` with the places and transitions of `b` added. */
export function unionDemand(a: SplitDemand, b: SplitDemand): SplitDemand {
  return { tested: new Set([...a.tested, ...b.tested]), forced: new Set([...a.forced, ...b.forced]) };
}

/**
 * {@link inFlightTransitions} with the places and transitions `demand` adds: a transition is split
 * when an output is in {@link nonMonotonePlaces} or in `demand.tested`, or when `demand.forced`
 * names it. Environment steps and completion steps stay atomic.
 * @internal
 */
export function inFlightTransitionsFor(
  net: PetriNet,
  environment: ReadonlySet<string>,
  demand: SplitDemand,
): string[] {
  const tested = nonMonotonePlaces(net);
  for (const p of demand.tested) tested.add(p);
  return [...net.transitions]
    .filter(t => !isCompletion(t) && !environment.has(t.name))
    .filter(t => demand.forced.has(t.name) || [...t.outputPlaces()].some(p => tested.has(p.name)))
    .map(t => t.name);
}

/**
 * The places a terminal stop can leave short ([EXEC-042], [VER-004]): the places `property` counts
 * and its waiver places, when it is a `quiescentCount` with a lower bound above zero and `net` has
 * a terminal place the waivers do not name. Every other quiescence property holds of a marking
 * whenever it holds of one with more tokens at a terminal rest, which every terminal excuses, so an
 * abandoned action cannot break it. Empty otherwise.
 * @internal
 */
export function quiescentCountDemand(net: PetriNet, property: SmtProperty): SplitDemand {
  if (property.type !== 'quiescent-count') return emptyDemand();
  const waived = new Set(property.waivedBy.map(p => p.name));
  const unwaivedTerminal = [...net.terminals].some(p => !waived.has(p.name));
  if (property.min === 0 || !unwaivedTerminal) return emptyDemand();
  return {
    tested: new Set([...property.places.map(p => p.name), ...waived]),
    forced: new Set(),
  };
}

/**
 * The transitions of `net` that can pre-empt another under conflict priority ([NU-052]): each `H`
 * with a strictly higher priority than some other transition that consumes one of `H`'s input
 * places. In net order.
 * @internal
 */
export function conflictPruners(net: PetriNet): string[] {
  const all = [...net.transitions];
  return all
    .filter(h => {
      const inputs = new Set([...h.inputPlaces()].map(p => p.name));
      return all.some(l => l.name !== h.name
        && h.priority > l.priority
        && [...l.inputPlaces()].some(p => inputs.has(p.name)));
    })
    .map(h => h.name);
}

/**
 * What conflict priority ([NU-052]) adds to the split: every pruner of {@link conflictPruners} is
 * forced, and its input and read places are tested, since more tokens there can enable it and so
 * disable the transition it pre-empts.
 * @internal
 */
export function conflictDemand(net: PetriNet): SplitDemand {
  const pruners = new Set(conflictPruners(net));
  const demand = emptyDemand();
  for (const h of net.transitions) {
    if (!pruners.has(h.name)) continue;
    for (const p of h.inputPlaces()) demand.tested.add(p.name);
    for (const a of h.reads) demand.tested.add(a.place.name);
    demand.forced.add(h.name);
  }
  return demand;
}

/**
 * Splits every transition of {@link inFlightTransitions} into a start and a completion (module
 * docs). `coloured` names the places whose tokens carry a ν name beyond the match specs' keys and
 * relay targets (the declared carrier places); a transition to split that is a ν-join or writes a
 * coloured place is refused. A mint ([NU-010]) mints only into a coloured place, so that covers it
 * too.
 */
export function splitInFlight(
  net: PetriNet,
  coloured: ReadonlySet<string> = new Set(),
  environment: ReadonlySet<string> = new Set(),
): InFlight {
  return splitInFlightFor(net, coloured, environment, emptyDemand());
}

/**
 * {@link splitInFlight} of the transitions {@link inFlightTransitionsFor} names under `demand`.
 * @internal
 */
export function splitInFlightFor(
  net: PetriNet,
  coloured: ReadonlySet<string>,
  environment: ReadonlySet<string>,
  demand: SplitDemand,
): InFlight {
  const split = inFlightTransitionsFor(net, environment, demand);
  if (split.length === 0) return { type: 'atomic' };
  const unsplittable = firstUnsplittable(net, coloured, split);
  if (unsplittable !== null) {
    const [t, cause] = unsplittable;
    const head = inFlightTransitions(net, environment).includes(t) ? refusalHead(t) : demandRefusalHead(t);
    return { type: 'refused', reason: `${head} ${cause}` };
  }
  const toSplit = new Set(split);
  const transitions: Transition[] = [];
  for (const t of net.transitions) {
    if (toSplit.has(t.name)) transitions.push(...halves(t));
    else transitions.push(t);
  }
  const rewritten = PetriNet.builder(net.name)
    .places(...net.places)
    .transitions(...transitions)
    .terminals(...net.terminals)
    .build();
  return { type: 'split', net: rewritten, split };
}

/**
 * The first transition of `split`, in net order, that the split cannot express, with the cause
 * ({@link refusalCause}). `coloured` is as for {@link splitInFlight}.
 * @internal
 */
export function firstUnsplittable(
  net: PetriNet,
  coloured: ReadonlySet<string>,
  split: readonly string[],
): [string, string] | null {
  const allColoured = new Set(coloured);
  for (const t of net.transitions) {
    if (t.matchSpec === null) continue;
    for (const k of t.matchSpec.keys) allColoured.add(k.place.name);
    for (const k of t.matchSpec.relays) allColoured.add(k.place.name);
  }
  const names = new Set<string>([
    ...[...net.places].map(p => p.name),
    ...[...net.transitions].map(t => t.name),
  ]);
  const toSplit = new Set(split);
  for (const t of net.transitions) {
    if (!toSplit.has(t.name)) continue;
    const cause = refusalCause(t, allColoured, names);
    if (cause !== null) return [t.name, cause];
  }
  return null;
}

/** The opening of the refusal of transition `name`. */
function refusalHead(name: string): string {
  return `transition '${name}' must be verified as two steps, since its action runs between ` +
    'consuming and depositing and another transition tests one of its outputs with an ' +
    'inhibitor, reset or drain (VER-004), but';
}

/**
 * The opening of the refusal of transition `name` when only a `SplitDemand` splits it: a
 * `quiescentCount` lower bound over a place it deposits into, on a net with a terminal place
 * (`quiescentCountDemand`).
 */
function demandRefusalHead(name: string): string {
  return `transition '${name}' must be verified as two steps, since a terminal place can stop ` +
    'the net while its action runs and the property\'s lower bound counts a place it ' +
    'deposits into (VER-004, EXEC-042), but';
}

/** Why `t` cannot be split, if it cannot: the clause that completes {@link refusalHead}, or `null`. */
function refusalCause(t: Transition, coloured: ReadonlySet<string>, names: ReadonlySet<string>): string | null {
  const name = t.name;
  if (t.matchSpec !== null) {
    return 'it is a ν-join, whose outputs carry the matched name (NU-020, NU-054)';
  }
  const outs = [...t.outputPlaces()].map(p => p.name).sort(compareCodePoints);
  const colouredOut = outs.find(p => coloured.has(p));
  if (colouredOut !== undefined) {
    return `it writes the coloured place '${colouredOut}', whose tokens carry a ν name`;
  }
  const forward = t.outputSpec === null ? null : multiTokenForward(t.outputSpec, t, false);
  if (forward !== null) {
    return `its timeout forwards input '${forward[0]}' to '${forward[1]}', one token per token ` +
      'consumed (IO-014), a count its completion step cannot see';
  }
  for (const added of [inFlightPlace(name), completionTransition(name)]) {
    if (names.has(added)) return `the net already uses the name '${added}' the split would add`;
  }
  return null;
}

/** The first `forwardInput` under a `timeout` whose source input is not `one`. */
function multiTokenForward(out: Out, t: Transition, underTimeout: boolean): [string, string] | null {
  switch (out.type) {
    case 'place':
      return null;
    case 'forward-input': {
      const spec: In | undefined = t.inputSpecs.find(s => s.place.name === out.from.name);
      const single = spec === undefined || spec.type === 'one';
      return underTimeout && !single ? [out.from.name, out.to.name] : null;
    }
    case 'timeout':
      return multiTokenForward(out.child, t, true);
    case 'and':
    case 'xor':
      for (const c of out.children) {
        const found = multiTokenForward(c, t, underTimeout);
        if (found !== null) return found;
      }
      return null;
  }
}

/** `t`'s output spec for its completion step: a `forwardInput(from, to)` leaf becomes `to`. */
function completionOutput(out: Out): Out {
  switch (out.type) {
    case 'place':
      return out;
    case 'forward-input':
      return { type: 'place', place: out.to };
    case 'and':
      return { type: 'and', children: out.children.map(completionOutput) };
    case 'xor':
      return { type: 'xor', children: out.children.map(completionOutput) };
    case 'timeout':
      return { type: 'timeout', afterMs: out.afterMs, child: completionOutput(out.child) };
  }
}

/** The start and the completion step of `t`. */
function halves(t: Transition): [Transition, Transition] {
  const p: Place<any> = place(inFlightPlace(t.name));
  const start = Transition.builder(t.name).timing(t.timing).priority(t.priority).action(t.action);
  if (t.placeAlias.size > 0) start.placeAlias(t.placeAlias);
  if (t.inputSpecs.length > 0) start.inputs(...t.inputSpecs);
  for (const arc of t.inhibitors) start.inhibitor(arc.place);
  for (const arc of t.reads) start.read(arc.place);
  for (const arc of t.resets) start.reset(arc.place);
  if (t.matchSpec !== null) start.match(t.matchSpec);
  start.outputs({ type: 'place', place: p });
  const end = Transition.builder(completionTransition(t.name))
    .timing(immediate())
    .priority(t.priority)
    .action(t.action)
    .inputs(one(p));
  if (t.outputSpec !== null) end.outputs(completionOutput(t.outputSpec));
  return [start.build(), end.build()];
}

/** The report line naming the split transitions. */
export function splitNote(split: readonly string[]): string {
  return `In-flight actions (VER-004): ${split.join(', ')} ${split.length === 1 ? 'is' : 'are'} ` +
    'verified in two steps, a start that consumes and a completion step (complete:<name>) that ' +
    'deposits, because another transition tests an output with an inhibitor, reset or drain and ' +
    'the executor fires other transitions while an action is in flight.\n';
}

/**
 * Why a verification splits beyond the arcs of its net (`SplitDemand`).
 * @internal
 */
export interface SplitReasons {
  /** Some transition tests an output non-monotonically ({@link nonMonotonePlaces}). */
  readonly tested: boolean;
  /** `quiescentCountDemand` added a transition. */
  readonly terminal: boolean;
  /** Conflict priority is applied with pruners (`conflictDemand`). */
  readonly conflict: boolean;
}

function plainReasons(r: SplitReasons): boolean {
  return !r.terminal && !r.conflict;
}

function reasonClauses(r: SplitReasons): string {
  const out: string[] = [];
  if (r.tested) out.push('another transition tests an output with an inhibitor, reset or drain');
  if (r.terminal) {
    out.push('a terminal place stops the net without waiting for an action in flight (EXEC-042) ' +
      'and the property\'s lower bound counts a place one of them deposits into');
  }
  if (r.conflict) {
    out.push('conflict priority (NU-052) reads whether a pruning transition is enabled, so a ' +
      'transition pre-empts no other while its own action is in flight');
  }
  return out.join('; ');
}

/**
 * The report line naming the split transitions when the verification added some
 * (`SplitDemand`); {@link splitNote} when it added none.
 * @internal
 */
export function splitNoteFor(split: readonly string[], reasons: SplitReasons): string {
  if (plainReasons(reasons)) return splitNote(split);
  return `In-flight actions (VER-004): ${split.join(', ')} ${split.length === 1 ? 'is' : 'are'} ` +
    'verified in two steps, a start that consumes and a completion step (complete:<name>) that ' +
    'deposits, because the executor fires other transitions while an action is in flight and ' +
    `${reasonClauses(reasons)}.\n`;
}

/**
 * The report line of a verdict reached with conflict priority ([NU-052]) turned off, because
 * `transition` has to be split for the pruning to hold and cannot be (`cause`, as
 * {@link firstUnsplittable} gives it).
 * @internal
 */
export function conflictOffNote(transition: string, cause: string): string {
  return 'Conflict priority (NU-052) is off: it holds only while no pruning transition, and no ' +
    'transition depositing into the input or read places of one, has an action in flight, ' +
    `which the verifier models by splitting them (VER-004), and transition '${transition}' ` +
    `cannot be split: ${cause}. Every enabled transition is explored.\n`;
}

/**
 * The report line of a verdict reached under `assumeAtomicFiring` on a net with a transition the
 * split would have applied to, when the verification added some (`SplitDemand`);
 * {@link atomicAssumptionNote} when it added none.
 * @internal
 */
export function atomicAssumptionNoteFor(split: readonly string[], reasons: SplitReasons): string {
  if (plainReasons(reasons)) return atomicAssumptionNote(split);
  return 'ASSUMPTION: every firing is atomic (the assume-atomic-firing option). The executor fires ' +
    `other transitions while an action of ${split.join(', ')} is in flight, and ${reasonClauses(reasons)} ` +
    '(VER-004); this verdict holds only for runs in which none of those actions is in flight when ' +
    'that matters.\n';
}

/**
 * The transitions a counterexample starts while an earlier firing of each is still in flight
 * ([CONC-002]): step `i` fires `transitions[i]` from `trace[i]`, and names a start whose place
 * `inflight:<name>` is marked there. First occurrence order, each once. Empty when the trace is
 * not aligned (`trace.length !== transitions.length + 1`).
 * @internal
 */
export function restartedTransitions(trace: readonly MarkingState[], transitions: readonly string[]): string[] {
  if (trace.length !== transitions.length + 1) return [];
  const out: string[] = [];
  transitions.forEach((t, i) => {
    if (trace[i]!.tokens(place(inFlightPlace(t))) > 0 && !out.includes(t)) out.push(t);
  });
  return out;
}

/**
 * The report line of a counterexample that restarts a transition in flight ([CONC-002],
 * {@link restartedTransitions}): the split lets a start fire again while its completion is
 * pending, as the Rust executor does, and the Java and TypeScript executors never do. `null` when
 * it restarts none.
 * @internal
 */
export function restartNote(trace: readonly MarkingState[], transitions: readonly string[]): string | null {
  const restarted = restartedTransitions(trace, transitions);
  if (restarted.length === 0) return null;
  const names = restarted.map(t => `'${t}'`).join(', ');
  const places = restarted.map(t => inFlightPlace(t)).join(', ');
  const [its, firing, is] = restarted.length === 1 ? ['its', 'firing', 'is'] : ['their', 'firings', 'are'];
  return `NOTE (CONC-002): the counterexample starts ${names} again while ${its} earlier ${firing} ${is} still ` +
    `in flight (${places} marked). The Rust executor starts a transition again while its action runs; ` +
    'the Java and TypeScript executors never do, so on them this counterexample may be a ' +
    'false alarm.\n';
}

/**
 * The name of the transition of the caller's net that `name` stands for: `t` for the completion
 * step `complete:<t>` of a split net that holds `inflight:<t>`, `name` itself otherwise.
 * @internal
 */
export function sourceTransition(net: PetriNet, name: string): string {
  const t = [...net.transitions].find(x => x.name === name);
  return t !== undefined && isCompletion(t) ? name.slice('complete:'.length) : name;
}

/** The report line of a verdict reached under `assumeAtomicFiring` on a net the split would change. */
export function atomicAssumptionNote(split: readonly string[]): string {
  return 'ASSUMPTION: every firing is atomic (the assume-atomic-firing option). Another transition ' +
    `tests an output of ${split.join(', ')} with an inhibitor, reset or drain, and the executor fires ` +
    'other transitions while an action is in flight (VER-004); this verdict holds only for runs in ' +
    'which no such test happens while one of those actions runs.\n';
}
