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

/** An encoded SMT-LIB2 script. */
export interface SmtEncoding {
  /** The script text. */
  readonly smt2: string;
  /** The number of flat places (the arity of `Reachable` in the flat encoding). */
  readonly placeCount: number;
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
 */
export function encode(
  flatNet: FlatNet,
  initialMarking: MarkingState,
  property: SmtProperty,
  invariants: readonly PInvariant[],
  sinkPlaces: ReadonlySet<Place<any>> = new Set(),
  produceProofs = false,
): SmtEncoding {
  const P = flatNet.places.length;
  const lines: string[] = [];
  const envInject = resolveEnvInjection(flatNet);

  if (produceProofs) lines.push('(set-option :produce-proofs true)');
  lines.push('(set-logic HORN)');
  lines.push('');

  lines.push(`(declare-fun Reachable (${ints(P).join(' ')}) Bool)`);
  lines.push('(declare-fun Error () Bool)');
  lines.push('');

  const mVars = vars(P, '');
  const mpVars = vars(P, 'p');

  const m0: string[] = [];
  for (let i = 0; i < P; i++) m0.push(String(initialMarking.tokens(flatNet.places[i]!)));
  lines.push(`(assert (Reachable ${m0.join(' ')}))`);
  lines.push('');

  for (const ft of flatNet.transitions) {
    lines.push(encodeTransitionRule(flatNet, ft, mVars, mpVars, invariants));
  }
  // Environment-injection rules (VER-006): NOT flat transitions, so the deadlock
  // encoding never sees them; no P-invariant strengthening, injection breaks
  // conservation on purpose.
  for (const inj of envInject) {
    lines.push(encodeInjectionRule(P, inj.pid, inj.bound, mVars, mpVars));
  }
  lines.push('');

  lines.push(encodeErrorRule(flatNet, property, mVars, sinkPlaces, envInject));
  lines.push('');

  // Under HORN/Spacer this is SAT when an inductive invariant excludes every
  // violating state (PROVEN) and UNSAT when none exists (VIOLATED).
  lines.push('(assert (not Error))');
  lines.push('(check-sat)');
  if (produceProofs) lines.push('(get-proof)');
  lines.push('(get-model)');

  return { smt2: lines.join('\n'), placeCount: P };
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

function quantified(names: readonly string[]): string {
  return names.map((v) => `(${v} Int)`).join(' ');
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
  invariants: readonly PInvariant[],
): string {
  const conditions = [`(Reachable ${mVars.join(' ')})`];
  conditions.push(...firingConditions(flatNet, ft, mVars, mpVars));
  conditions.push(...invariantConditions(invariants, mpVars));
  conditions.push(...envBoundConditions(flatNet, mpVars));
  const body = `(and ${conditions.join('\n            ')})`;
  return `(assert (forall (${quantified([...mVars, ...mpVars])})\n  (=> ${body}\n      (Reachable ${mpVars.join(' ')}))))`;
}

function encodeInjectionRule(
  P: number,
  pid: number,
  bound: number | null,
  mVars: readonly string[],
  mpVars: readonly string[],
): string {
  const conditions = [`(Reachable ${mVars.join(' ')})`];
  conditions.push(...injectionConditions(P, pid, bound, mVars, mpVars));
  const body = `(and ${conditions.join('\n            ')})`;
  return `(assert (forall (${quantified([...mVars, ...mpVars])})\n  (=> ${body}\n      (Reachable ${mpVars.join(' ')}))))`;
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
export function encodeStepRelationSmt2(flatNet: FlatNet): string {
  const P = flatNet.places.length;
  const mVars = vars(P, '');
  const mpVars = vars(P, 'p');
  const disjuncts: string[] = [];
  for (const ft of flatNet.transitions) {
    const conditions = firingConditions(flatNet, ft, mVars, mpVars);
    conditions.push(...envBoundConditions(flatNet, mpVars));
    disjuncts.push(conjoin(conditions));
  }
  for (const inj of resolveEnvInjection(flatNet)) {
    disjuncts.push(conjoin(injectionConditions(P, inj.pid, inj.bound, mVars, mpVars)));
  }
  if (disjuncts.length === 0) return 'false';
  if (disjuncts.length === 1) return disjuncts[0]!;
  return `(or ${disjuncts.join('\n    ')})`;
}

function encodeErrorRule(
  flatNet: FlatNet,
  property: SmtProperty,
  mVars: readonly string[],
  sinkPlaces: ReadonlySet<Place<any>>,
  envInject: readonly Injection[],
): string {
  const violation = encodePropertyViolation(flatNet, property, mVars, sinkPlaces, envInject);
  return `(assert (forall (${quantified(mVars)})\n  (=> (and (Reachable ${mVars.join(' ')}) ${violation})\n      Error)))`;
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
): string {
  switch (property.type) {
    case 'deadlock-free':
      return encodeDeadlock(flatNet, mVars, sinkPlaces, envInject);
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
    case 'joined-or-dead-lettered': {
      // NU-040: a quiescent marking still holding a `pending` token.
      const deadlock = encodeDeadlock(flatNet, mVars, sinkPlaces, envInject);
      const pid = flatNet.placeIndex.get(property.pending.name);
      return pid == null ? 'false' : `(and ${deadlock} (>= ${mVars[pid]} 1))`;
    }
  }
}

/**
 * Deadlock: every transition is disabled. Environment inputs are treated as
 * injectable (VER-006): an input/read on an injectable env place is NOT a reason the
 * transition is disabled (AlwaysAvailable always satisfies it, Bounded(k) iff the
 * demand is at most k), so a reactive net merely waiting for input is not a deadlock;
 * only a genuinely stuck marking is. Declared sinks (VER-002) each contribute
 * `M[sink] = 0`.
 */
function encodeDeadlock(
  flatNet: FlatNet,
  mVars: readonly string[],
  sinkPlaces: ReadonlySet<Place<any>>,
  envInject: readonly Injection[],
): string {
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
    if (disableReasons.length === 0) return 'false';
    disabledConditions.push(`(or ${disableReasons.join(' ')})`);
  }
  for (const pid of indexOrdered(flatNet, sinkPlaces)) {
    disabledConditions.push(`(= ${mVars[pid]} 0)`);
  }
  return disabledConditions.length === 0 ? 'true' : `(and ${disabledConditions.join('\n         ')})`;
}

/** Env-injectable bound map, index to cap (`null` = unbounded), for the coloured encoder. */
export function injectionMap(flatNet: FlatNet): Map<number, number | null> {
  const out = new Map<number, number | null>();
  for (const inj of resolveEnvInjection(flatNet)) out.set(inj.pid, inj.bound);
  return out;
}
