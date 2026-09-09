/**
 * @module smt-encoder
 *
 * Encodes a flattened Petri net as Constrained Horn Clauses (CHC) in SMT-LIB2 text
 * for Z3's Spacer engine (VER-013).
 *
 * The net's state space is modeled as integer vectors (one variable per place = token
 * count). Three rule types:
 *
 * 1. **Init**: `(assert (Reachable M0))` — the initial marking is reachable
 * 2. **Transition**: `Reachable(M') :- Reachable(M) ∧ enabled(M,t) ∧ fire(M,M',t) ∧
 *    M' ≥ 0 ∧ invariants(M') ∧ env-bounds(M')` — one rule per flat transition, plus
 *    one env-injection rule per injected environment place (VER-006)
 * 3. **Error**: `Error :- Reachable(M) ∧ violation(M)`; `(assert (not Error))`, so
 *    `sat` is PROVEN and `unsat` is VIOLATED
 *
 * With the state equation (VER-016, {@link encodeNet}) the state is `(M, n)` — one
 * firing counter per flat transition — and every transition rule also conjoins
 * `M' = M0 + C·n'`, which hands Spacer every linear consequence of the marking
 * equation (the inequality conservation laws it cannot invent) at no enumeration cost.
 *
 * The emitted script is byte-identical to the Rust reference (`smt_encoder.rs`) and
 * the Java port for the same input: places in code-point order of their names, the
 * property's places, sinks, env bounds and injections in place-index order,
 * invariants in the order the verifier canonicalised.
 */
import type { FlatNet } from '../encoding/flat-net.js';
import type { FlatTransition } from '../encoding/flat-transition.js';
import type { MarkingState } from '../marking-state.js';
import type { SmtProperty } from '../smt-property.js';
import type { PInvariant } from '../invariant/p-invariant.js';
import type { Place } from '../../core/place.js';
import { strandingExcuses, type ConditionalSinks } from '../rest-set.js';
import { nonlinearPlaces } from '../invariant/p-invariant-computer.js';

/** An encoded SMT-LIB2 script. */
export interface SmtEncoding {
  /** The script text. */
  readonly smt2: string;
  /** The number of flat places (the leading arguments of `Reachable` in the flat encoding). */
  readonly placeCount: number;
  /**
   * The number of firing counters that follow the places in `Reachable` (VER-016):
   * one per flat transition when the state equation is encoded, else 0.
   */
  readonly counterCount: number;
}

/** Options of {@link encodeNet}. */
export interface EncodeOptions {
  /** Declared sink places (VER-002). */
  readonly sinkPlaces?: ReadonlySet<Place<any>>;
  /** Emit `:produce-proofs` and `(get-proof)` so an `unsat` reply carries the refutation the replay decodes. */
  readonly produceProofs?: boolean;
  /** Conditional sinks (VER-014); read by `deadlock-free` only. */
  readonly conditionalSinks?: readonly ConditionalSinks[];
  /**
   * Carry one firing counter per flat transition and conjoin the marking equation
   * `M' = M0 + C·n'` (VER-016) into every rule body. Off by default (scripts stay
   * byte-identical).
   */
  readonly stateEquation?: boolean;
}

/** An injected environment place: its flat index and its cap (`null` = unbounded). */
export interface Injection {
  readonly pid: number;
  readonly bound: number | null;
}

/**
 * Encodes the net and property as a HORN script.
 *
 * @param produceProofs emit `:produce-proofs` and `(get-proof)` so an `unsat` reply
 *   carries the refutation the replay decodes
 * @param conditionalSinks places where a token may rest while a marker is marked
 *   (VER-014); read by `deadlock-free` only
 */
export function encode(
  flatNet: FlatNet,
  initialMarking: MarkingState,
  property: SmtProperty,
  invariants: readonly PInvariant[],
  sinkPlaces: ReadonlySet<Place<any>> = new Set(),
  produceProofs = false,
  conditionalSinks: readonly ConditionalSinks[] = [],
): SmtEncoding {
  return encodeNet(flatNet, initialMarking, property, invariants, { sinkPlaces, produceProofs, conditionalSinks });
}

/**
 * {@link encode} with named options. With `stateEquation` (VER-016) the state carries
 * one firing counter per flat transition after the places: `Reachable(M, n)`, the
 * initial fact has `n = 0`, transition `k`'s rule increments `n_k` and copies the
 * others, an injection rule copies them all, and every transition rule's body
 * conjoins `m'_p = M0_p + Σ_t C[p][t]·n'_t` for each place whose column is exact
 * (no consume-all / reset arc, not injected) together with `n' ≥ 0`. The error rule
 * quantifies the counters and constrains only the marking.
 */
export function encodeNet(
  flatNet: FlatNet,
  initialMarking: MarkingState,
  property: SmtProperty,
  invariants: readonly PInvariant[],
  options: EncodeOptions = {},
): SmtEncoding {
  const sinkPlaces = options.sinkPlaces ?? new Set<Place<any>>();
  const produceProofs = options.produceProofs ?? false;
  const conditionalSinks = options.conditionalSinks ?? [];
  const P = flatNet.places.length;
  const T = options.stateEquation ? flatNet.transitions.length : 0;
  const lines: string[] = [];
  const envInject = resolveEnvInjection(flatNet);

  if (produceProofs) lines.push('(set-option :produce-proofs true)');
  lines.push('(set-logic HORN)');
  lines.push('');

  lines.push(`(declare-fun Reachable (${ints(P + T).join(' ')}) Bool)`);
  lines.push('(declare-fun Error () Bool)');
  lines.push('');

  const mVars = vars(P, '');
  const mpVars = vars(P, 'p');
  const nVars = counterVars(T, '');
  const npVars = counterVars(T, 'p');

  const m0: string[] = [];
  for (let i = 0; i < P; i++) m0.push(String(initialMarking.tokens(flatNet.places[i]!)));
  for (let k = 0; k < T; k++) m0.push('0');
  lines.push(`(assert (Reachable ${m0.join(' ')}))`);
  lines.push('');

  const equation = T > 0 ? stateEquationConditions(flatNet, initialMarking, npVars) : [];
  for (let k = 0; k < flatNet.transitions.length; k++) {
    const ft = flatNet.transitions[k]!;
    const strengthening = [...invariantConditions(invariants, mpVars)];
    if (T > 0) strengthening.push(...counterConditions(k, nVars, npVars), ...equation);
    lines.push(encodeTransitionRule(flatNet, ft, mVars, mpVars, nVars, npVars, strengthening));
  }
  // Environment-injection rules (VER-006): NOT flat transitions, so the deadlock
  // encoding never sees them; no P-invariant strengthening, injection breaks
  // conservation on purpose. The counters are carried unchanged (VER-016).
  for (const inj of envInject) {
    lines.push(encodeInjectionRule(P, inj.pid, inj.bound, mVars, mpVars, nVars, npVars));
  }
  lines.push('');

  lines.push(encodeErrorRule(flatNet, property, mVars, nVars, sinkPlaces, envInject, conditionalSinks));
  lines.push('');

  // Under HORN/Spacer this is SAT when an inductive invariant excludes every
  // violating state (PROVEN) and UNSAT when none exists (VIOLATED).
  lines.push('(assert (not Error))');
  lines.push('(check-sat)');
  if (produceProofs) lines.push('(get-proof)');
  lines.push('(get-model)');

  return { smt2: lines.join('\n'), placeCount: P, counterCount: T };
}

/** The injected environment places in place-index order. */
export function resolveEnvInjection(flatNet: FlatNet): Injection[] {
  const out: Injection[] = [];
  for (const [name, bound] of flatNet.environmentInjection) {
    const pid = flatNet.placeIndex.get(name);
    if (pid != null) out.push({ pid, bound });
  }
  out.sort((a, b) => a.pid - b.pid);
  return out;
}

/** The bounded environment places (legacy post-cap) in place-index order. */
function envBounds(flatNet: FlatNet): Array<[number, number]> {
  const out: Array<[number, number]> = [];
  for (const [name, max] of flatNet.environmentBounds) {
    const pid = flatNet.placeIndex.get(name);
    if (pid != null) out.push([pid, max]);
  }
  out.sort((a, b) => a[0] - b[0]);
  return out;
}

function ints(n: number): string[] {
  return new Array<string>(n).fill('Int');
}

function vars(P: number, suffix: string): string[] {
  const out: string[] = [];
  for (let i = 0; i < P; i++) out.push(`m${i}${suffix}`);
  return out;
}

/** `n0..n{T-1}` (`suffix` = `'p'` for the primed counters), empty when `T` is 0. */
function counterVars(T: number, suffix: string): string[] {
  const out: string[] = [];
  for (let k = 0; k < T; k++) out.push(`n${k}${suffix}`);
  return out;
}

function quantified(names: readonly string[]): string {
  return names.map((v) => `(${v} Int)`).join(' ');
}

// === State equation (VER-016) ===

/**
 * The places whose column of the incidence matrix is exact in every step: no
 * consume-all / reset arc on them (H1) and not injected (H3'). Only these carry a
 * marking-equation row; the others are unconstrained by it.
 */
export function equationPlaces(flatNet: FlatNet): number[] {
  const excluded = new Set<number>(nonlinearPlaces(flatNet));
  for (const inj of resolveEnvInjection(flatNet)) excluded.add(inj.pid);
  const out: number[] = [];
  for (let p = 0; p < flatNet.places.length; p++) if (!excluded.has(p)) out.push(p);
  return out;
}

/**
 * The counter update of transition `fired` (`-1` for an injection step, which fires
 * no counted transition): `n'_k = n_k + 1` for the fired one, `n'_j = n_j` for the
 * rest, then `n' ≥ 0`.
 */
export function counterConditions(fired: number, nVars: readonly string[], npVars: readonly string[]): string[] {
  const conditions: string[] = [];
  for (let k = 0; k < nVars.length; k++) {
    conditions.push(k === fired ? `(= ${npVars[k]} (+ ${nVars[k]} 1))` : `(= ${npVars[k]} ${nVars[k]})`);
  }
  for (let k = 0; k < npVars.length; k++) conditions.push(`(>= ${npVars[k]} 0)`);
  return conditions;
}

/**
 * The marking equation over the given marking and counter variables: for every
 * place of {@link equationPlaces}, `m_p = M0_p + Σ_t C[p][t]·n_t` over the flat
 * transitions with a non-zero effect on `p`, in transition order. A coefficient of
 * 1 is the bare counter, −1 is `(- n)`, any other `(* c n)` with a negative `c`
 * written `(- k)`.
 */
export function stateEquationConditions(
  flatNet: FlatNet,
  initialMarking: MarkingState,
  nVars: readonly string[],
  mVars: readonly string[] = vars(flatNet.places.length, 'p'),
): string[] {
  const conditions: string[] = [];
  for (const p of equationPlaces(flatNet)) {
    const terms: string[] = [];
    for (let t = 0; t < flatNet.transitions.length; t++) {
      const ft = flatNet.transitions[t]!;
      const c = ft.postVector[p]! - ft.preVector[p]!;
      if (c === 0) continue;
      terms.push(c === 1 ? nVars[t]! : c === -1 ? `(- ${nVars[t]})` : c > 0 ? `(* ${c} ${nVars[t]})` : `(* (- ${-c}) ${nVars[t]})`);
    }
    const m0 = initialMarking.tokens(flatNet.places[p]!);
    conditions.push(terms.length === 0 ? `(= ${mVars[p]} ${m0})` : `(= ${mVars[p]} (+ ${m0} ${terms.join(' ')}))`);
  }
  return conditions;
}

// === Shared condition emitters ===
//
// Emitted by BOTH the CHC rule encoding and the plain-SMT step relation
// (encodeStepRelationSmt2) the certificate check uses, so the two cannot drift.

/**
 * Enablement + firing + non-negativity conjuncts for one flat transition:
 * `enabled(M, t)`, `fire(M, M', t)`, `M' >= 0`. Excludes the `Reachable` body atom,
 * the P-invariant strengthening and the env bounds.
 */
function firingConditions(
  flatNet: FlatNet,
  ft: FlatTransition,
  mVars: readonly string[],
  mpVars: readonly string[],
): string[] {
  const P = flatNet.places.length;
  const conditions: string[] = [];
  for (let i = 0; i < P; i++) {
    if (ft.preVector[i]! > 0) conditions.push(`(>= ${mVars[i]} ${ft.preVector[i]})`);
  }
  for (const inh of ft.inhibitorPlaces) conditions.push(`(= ${mVars[inh]} 0)`);
  for (const rd of ft.readPlaces) conditions.push(`(>= ${mVars[rd]} 1)`);
  for (let i = 0; i < P; i++) {
    if (ft.resetPlaces.includes(i) || ft.consumeAll[i]) {
      // Reset / consume-all: clear then add post.
      conditions.push(`(= ${mpVars[i]} ${ft.postVector[i]})`);
    } else {
      const delta = ft.postVector[i]! - ft.preVector[i]!;
      if (delta > 0) conditions.push(`(= ${mpVars[i]} (+ ${mVars[i]} ${delta}))`);
      else if (delta < 0) conditions.push(`(= ${mpVars[i]} (- ${mVars[i]} ${-delta}))`);
      else conditions.push(`(= ${mpVars[i]} ${mVars[i]})`);
    }
  }
  for (let i = 0; i < P; i++) conditions.push(`(>= ${mpVars[i]} 0)`);
  return conditions;
}

/**
 * P-invariant conjuncts over the given marking variables. The step relation never
 * emits these: the certificate check keeps its relation UNSTRENGTHENED and conjoins
 * them into the candidate instead, where the VCs re-prove them.
 */
export function invariantConditions(invariants: readonly PInvariant[], names: readonly string[]): string[] {
  const conditions: string[] = [];
  for (const inv of invariants) {
    const terms = [...inv.support].sort((a, b) => a - b).map((i) => `(* ${inv.weights[i]} ${names[i]})`);
    if (terms.length === 0) continue;
    const sum = terms.length === 1 ? terms[0]! : `(+ ${terms.join(' ')})`;
    conditions.push(`(= ${sum} ${inv.constant})`);
  }
  return conditions;
}

/** Environment post-cap conjuncts on the next marking (legacy Bounded mode). */
function envBoundConditions(flatNet: FlatNet, mpVars: readonly string[]): string[] {
  return envBounds(flatNet).map(([pid, max]) => `(<= ${mpVars[pid]} ${max})`);
}

/**
 * Guard + column-update conjuncts for one env-injection step (VER-006):
 * `[m_pid < bound]`, `m'_pid = m_pid + 1`, all other columns copied.
 */
function injectionConditions(
  P: number,
  pid: number,
  bound: number | null,
  mVars: readonly string[],
  mpVars: readonly string[],
): string[] {
  const conditions: string[] = [];
  if (bound != null) conditions.push(`(< ${mVars[pid]} ${bound})`);
  for (let i = 0; i < P; i++) {
    if (i === pid) conditions.push(`(= ${mpVars[i]} (+ ${mVars[i]} 1))`);
    else conditions.push(`(= ${mpVars[i]} ${mVars[i]})`);
  }
  return conditions;
}

function encodeTransitionRule(
  flatNet: FlatNet,
  ft: FlatTransition,
  mVars: readonly string[],
  mpVars: readonly string[],
  nVars: readonly string[],
  npVars: readonly string[],
  strengthening: readonly string[],
): string {
  const conditions = [`(Reachable ${[...mVars, ...nVars].join(' ')})`];
  conditions.push(...firingConditions(flatNet, ft, mVars, mpVars));
  conditions.push(...strengthening);
  conditions.push(...envBoundConditions(flatNet, mpVars));
  const body = `(and ${conditions.join('\n            ')})`;
  const quantifiedVars = quantified([...mVars, ...mpVars, ...nVars, ...npVars]);
  return `(assert (forall (${quantifiedVars})\n  (=> ${body}\n      (Reachable ${[...mpVars, ...npVars].join(' ')}))))`;
}

function encodeInjectionRule(
  P: number,
  pid: number,
  bound: number | null,
  mVars: readonly string[],
  mpVars: readonly string[],
  nVars: readonly string[],
  npVars: readonly string[],
): string {
  const conditions = [`(Reachable ${[...mVars, ...nVars].join(' ')})`];
  conditions.push(...injectionConditions(P, pid, bound, mVars, mpVars));
  if (nVars.length > 0) conditions.push(...counterConditions(-1, nVars, npVars));
  const body = `(and ${conditions.join('\n            ')})`;
  const quantifiedVars = quantified([...mVars, ...mpVars, ...nVars, ...npVars]);
  return `(assert (forall (${quantifiedVars})\n  (=> ${body}\n      (Reachable ${[...mpVars, ...npVars].join(' ')}))))`;
}

/**
 * Joins conjuncts into one formula (`true` when empty, the bare conjunct when
 * singleton, since SMT-LIB `and` wants at least two arguments).
 */
export function conjoin(conditions: readonly string[]): string {
  if (conditions.length === 0) return 'true';
  if (conditions.length === 1) return conditions[0]!;
  return `(and ${conditions.join(' ')})`;
}

/**
 * The net's one-step relation `T(M, M')` as one plain SMT-LIB2 formula over the free
 * variables `m0..` / `m0p..`: the disjunction of every flat transition firing and
 * every env-injection step (VER-006). This is the UNSTRENGTHENED relation the
 * certificate check validates against: it shares the condition emitters with the CHC
 * path but omits the P-invariant conjuncts, so a certificate poisoned by a wrong
 * invariant cannot re-certify itself.
 */
export function encodeStepRelationSmt2(flatNet: FlatNet, stateEquation = false): string {
  const P = flatNet.places.length;
  const T = stateEquation ? flatNet.transitions.length : 0;
  const mVars = vars(P, '');
  const mpVars = vars(P, 'p');
  const nVars = counterVars(T, '');
  const npVars = counterVars(T, 'p');
  const disjuncts: string[] = [];
  for (let k = 0; k < flatNet.transitions.length; k++) {
    const ft = flatNet.transitions[k]!;
    const conditions = firingConditions(flatNet, ft, mVars, mpVars);
    // The counters move with the step (VER-016); the marking equation itself is
    // strengthening and stays out — the candidate carries it and the VCs re-prove it.
    if (T > 0) conditions.push(...counterConditions(k, nVars, npVars));
    conditions.push(...envBoundConditions(flatNet, mpVars));
    disjuncts.push(conjoin(conditions));
  }
  for (const inj of resolveEnvInjection(flatNet)) {
    const conditions = injectionConditions(P, inj.pid, inj.bound, mVars, mpVars);
    if (T > 0) conditions.push(...counterConditions(-1, nVars, npVars));
    disjuncts.push(conjoin(conditions));
  }
  if (disjuncts.length === 0) return 'false';
  if (disjuncts.length === 1) return disjuncts[0]!;
  return `(or ${disjuncts.join('\n    ')})`;
}

function encodeErrorRule(
  flatNet: FlatNet,
  property: SmtProperty,
  mVars: readonly string[],
  nVars: readonly string[],
  sinkPlaces: ReadonlySet<Place<any>>,
  envInject: readonly Injection[],
  conditionalSinks: readonly ConditionalSinks[],
): string {
  const violation = encodePropertyViolation(flatNet, property, mVars, sinkPlaces, envInject, conditionalSinks);
  const state = [...mVars, ...nVars];
  return `(assert (forall (${quantified(state)})\n  (=> (and (Reachable ${state.join(' ')}) ${violation})\n      Error)))`;
}

/** The flat indices of the given places that resolve, ascending and deduplicated. */
export function indexOrdered(flatNet: FlatNet, places: Iterable<Place<any>>): number[] {
  const idx = new Set<number>();
  for (const place of places) {
    const i = flatNet.placeIndex.get(place.name);
    if (i != null) idx.add(i);
  }
  return [...idx].sort((a, b) => a - b);
}

/**
 * The property-violation condition `Bad(M)` over `mVars`. Also used by the
 * certificate check's safety VC, which must test against exactly the violation the
 * error rule encodes. A place the net does not declare contributes nothing; the
 * verifier refuses such a property before encoding.
 */
export function encodePropertyViolation(
  flatNet: FlatNet,
  property: SmtProperty,
  mVars: readonly string[],
  sinkPlaces: ReadonlySet<Place<any>>,
  envInject: readonly Injection[],
  conditionalSinks: readonly ConditionalSinks[] = [],
): string {
  switch (property.type) {
    // DeadlockFree (VER-002): a quiescent marking that STRANDS a token — holds one
    // in a place where resting is not permitted. The empty marking strands nothing
    // and is therefore not a violation (AC4). A conditional sink (VER-014) is
    // stranded only while every marker that would excuse it is unmarked.
    case 'deadlock-free': {
      const conditions = encodeQuiescent(flatNet, mVars, envInject);
      if (conditions == null) return 'false';
      const stranded = strandedConditions(strandingExcuses(flatNet, sinkPlaces, conditionalSinks), mVars);
      // Every place is a declared sink: nothing can ever be stranded.
      if (stranded.length === 0) return 'false';
      conditions.push(`(or ${stranded.join(' ')})`);
      return joinConditions(conditions);
    }
    // TerminatesAtSink (VER-002): a quiescent marking that reached NO declared sink.
    // This is the predicate DeadlockFree carried before the VER-002 split, unchanged.
    case 'terminates-at-sink': {
      const conditions = encodeQuiescent(flatNet, mVars, envInject);
      if (conditions == null) return 'false';
      for (const pid of indexOrdered(flatNet, sinkPlaces)) {
        conditions.push(`(= ${mVars[pid]} 0)`);
      }
      return joinConditions(conditions);
    }
    case 'mutual-exclusion': {
      const conditions = indexOrdered(flatNet, [property.p1, property.p2]).map((i) => `(>= ${mVars[i]} 1)`);
      return conditions.length === 0 ? 'false' : `(and ${conditions.join(' ')})`;
    }
    case 'place-bound':
    case 'branch-place-bound': {
      // BranchPlaceBound is the ν-net budget lever (NU-040): a count bound, encoded
      // like PlaceBound.
      const pid = flatNet.placeIndex.get(property.place.name);
      return pid == null ? 'false' : `(> ${mVars[pid]} ${property.bound})`;
    }
    case 'unreachable': {
      const conditions = indexOrdered(flatNet, property.places).map((i) => `(>= ${mVars[i]} 1)`);
      return conditions.length === 0 ? 'false' : `(and ${conditions.join(' ')})`;
    }
    // JoinedOrDeadLettered (NU-040 AC4): a quiescent state that still holds a
    // `pending` token is a stranded correlation group. Carries NO sink clause — a
    // declared sink must not excuse a stranded group.
    case 'joined-or-dead-lettered': {
      const pid = flatNet.placeIndex.get(property.pending.name);
      // Unknown pending place name: no state can violate.
      if (pid == null) return 'false';
      const conditions = encodeQuiescent(flatNet, mVars, envInject);
      if (conditions == null) return 'false';
      conditions.push(`(>= ${mVars[pid]} 1)`);
      return joinConditions(conditions);
    }
  }
}

/**
 * One "a token is stranded here" disjunct per place where resting is not always
 * permitted: `(>= m 1)`, conjoined with `(= marker 0)` for every marker whose
 * presence would excuse it (VER-014), markers in place-index order. Shared with the
 * name-coloured encoder through `counts`, which renders a place's count term.
 */
export function strandedConditions(
  excuses: readonly (readonly number[] | null)[],
  counts: readonly string[],
): string[] {
  const stranded: string[] = [];
  for (let pid = 0; pid < excuses.length; pid++) {
    const markers = excuses[pid];
    if (markers == null) continue;
    if (markers.length === 0) {
      stranded.push(`(>= ${counts[pid]} 1)`);
    } else {
      stranded.push(`(and (>= ${counts[pid]} 1) ${markers.map(k => `(= ${counts[k]} 0)`).join(' ')})`);
    }
  }
  return stranded;
}

/**
 * Joins violation conjuncts into the final `Bad(M)` term. An empty conjunction is
 * vacuously true — a net with no transitions is quiescent everywhere.
 */
function joinConditions(conditions: readonly string[]): string {
  return conditions.length === 0 ? 'true' : `(and ${conditions.join('\n         ')})`;
}

/**
 * Quiescence: every transition is disabled.
 *
 * Shared core of the three quiescence-sensitive properties (VER-002 DeadlockFree
 * and TerminatesAtSink, NU-040 JoinedOrDeadLettered). Each conjoins its own clause
 * on top and none is encoded here, so a change to one predicate cannot silently
 * move the others — which is exactly how the sink clause leaked into
 * JoinedOrDeadLettered before NU-040 AC4.
 *
 * Returns `null` when some transition is enabled in every marking: no quiescent
 * marking exists, so every property built on this is unviolatable.
 *
 * Environment inputs are treated as injectable (VER-006): an input/read on an
 * injectable env place is NOT a reason the transition is disabled (AlwaysAvailable
 * always satisfies it, Bounded(k) iff the demand is at most k), so a reactive net
 * merely waiting for input is not reported as quiescent; only a genuinely stuck
 * marking is.
 */
function encodeQuiescent(
  flatNet: FlatNet,
  mVars: readonly string[],
  envInject: readonly Injection[],
): string[] | null {
  const envBound = new Map<number, number | null>();
  for (const inj of envInject) envBound.set(inj.pid, inj.bound);
  const disabledConditions: string[] = [];
  for (const ft of flatNet.transitions) {
    const disableReasons: string[] = [];
    let permanentlyDisabled = false;
    for (let i = 0; i < flatNet.places.length; i++) {
      if (ft.preVector[i]! > 0) {
        if (envBound.has(i)) {
          const k = envBound.get(i)!;
          if (k != null && ft.preVector[i]! > k) permanentlyDisabled = true;
          continue;
        }
        disableReasons.push(`(< ${mVars[i]} ${ft.preVector[i]})`);
      }
    }
    for (const inh of ft.inhibitorPlaces) disableReasons.push(`(> ${mVars[inh]} 0)`);
    for (const rd of ft.readPlaces) {
      if (envBound.has(rd)) {
        const k = envBound.get(rd)!;
        if (k != null && k < 1) permanentlyDisabled = true;
        continue;
      }
      disableReasons.push(`(< ${mVars[rd]} 1)`);
    }
    if (permanentlyDisabled) {
      disabledConditions.push('true');
      continue;
    }
    // Transition is always enabled (possibly via injection) — never quiescent.
    if (disableReasons.length === 0) return null;
    disabledConditions.push(`(or ${disableReasons.join(' ')})`);
  }
  return disabledConditions;
}

/**
 * Whether NO marking of this net can be quiescent, because some transition is
 * enabled in every marking — an environment-gated one whose input injection can
 * always satisfy ([VER-006]).
 *
 * Every quiescence property is then unviolatable and comes back `proven` for a
 * reason that has nothing to do with the net's own behaviour: an open net with an
 * always-available source never comes to rest, so "no reachable quiescent marking
 * strands a token" is vacuously true. The verdict is correct and says nothing, and
 * a caller reading it as "this workflow completes properly" is misreading it, so
 * the verifier says so in the report.
 */
export function quiescenceUnreachable(flatNet: FlatNet, envInject: readonly Injection[]): boolean {
  return encodeQuiescent(flatNet, vars(flatNet.places.length, ''), envInject) === null;
}

/** Env-injectable bound map, index to cap (`null` = unbounded), for the coloured encoder. */
export function injectionMap(flatNet: FlatNet): Map<number, number | null> {
  const out = new Map<number, number | null>();
  for (const inj of resolveEnvInjection(flatNet)) out.set(inj.pid, inj.bound);
  return out;
}
