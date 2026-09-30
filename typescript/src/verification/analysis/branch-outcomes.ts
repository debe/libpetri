/**
 * @module branch-outcomes
 *
 * What one firing of a transition can deposit, for every analysis that expands a transition's
 * output spec: the flattener behind the SMT routes, the state-class graph (the enumeration
 * route, [VER-017]), the ν name-partition graph (Route B) and everything built on those.
 *
 * A firing ends one of two ways, and they deposit differently:
 *
 * - **The action completes** and writes a branch of the spec ([IO-015]). A branch is a set of
 *   places and the analyses model one token per place of it ([IO-016]); a `ForwardInput` leaf
 *   is then an ordinary claim on its `to` place.
 * - **The action's `Timeout` fires** ([IO-013]). The marking receives the timeout child's tokens
 *   *and nothing else* — no sibling of the `Timeout` — and a `ForwardInput(from, to)` leaf
 *   deposits one token in `to` **per token the firing consumed from `from`** ([IO-014]): `n` for
 *   `exactly(n)`, the whole drained batch for `all` / `atLeast`.
 *
 * Every analysis used to read the timeout child as if the action had written it: one token per
 * named place, siblings included. On `exactly(2, a) -> xor(c, timeout(50, forwardInput(a, b)))`
 * that deposits one token in `b` where the executor deposits two, and `placeBound(b, 1)` was
 * proven by the structural, fixpoint and enumeration routes alike.
 *
 * {@link outcomes} lists the action outcomes first, in `enumerateBranches` order — so a flat
 * transition keeps its `_b<i>` name and a graph edge its branch index — then the timeout outcome
 * when it differs from every action outcome. It differs exactly when the child forwards a batch
 * that is not one token, or the `Timeout` has a sibling in its branch; on every other spec the
 * list is the one the analyses always used.
 *
 * A forward of an `all` / `atLeast` input deposits a marking-dependent count (a `drained`
 * deposit) — a transfer. The graphs resolve it from the marking they fire in, so the state-space
 * enumeration ([VER-017]), the timed state-class graph and Route B decide such a net exactly; the
 * flat encodings cannot express it, so the verifier refuses it on the linear routes only
 * ({@link drainedForward}).
 */
import type { PetriNet } from '../../core/petri-net.js';
import type { Place } from '../../core/place.js';
import type { Transition } from '../../core/transition.js';
import { type Out, enumerateBranches } from '../../core/out.js';
import { requiredCount } from '../../core/in.js';
import { compareCodePoints } from '../../core/internal/code-point-order.js';

/**
 * Tokens one outcome deposits into one place: a fixed count (1 for a place an action writes or
 * a timeout mints, `n` for a timeout forward from a `one` / `exactly(n)` input), or every token
 * the firing drained from `from` (a timeout forward from an `all` / `atLeast` input, [IO-014]).
 */
export type Deposit =
  | { readonly type: 'tokens'; readonly count: number }
  | { readonly type: 'drained'; readonly from: Place<any> };

/** One place an outcome deposits into. */
export interface OutcomeDeposit {
  readonly place: Place<any>;
  readonly deposit: Deposit;
}

/** One way a firing of a transition can end. */
export interface Outcome {
  /** Each place this outcome deposits into, once, in code-point order of its name. */
  readonly deposits: readonly OutcomeDeposit[];
  /**
   * The same places as a set: the ν name layer reads which places receive a token, and rejects
   * from its fragment a coloured place that receives any count but one.
   */
  readonly places: ReadonlySet<Place<any>>;
}

const ONE: Deposit = { type: 'tokens', count: 1 };

function makeOutcome(deposits: Map<string, OutcomeDeposit>): Outcome {
  const sorted = [...deposits.values()].sort((x, y) => compareCodePoints(x.place.name, y.place.name));
  return { deposits: sorted, places: new Set(sorted.map(d => d.place)) };
}

/** The outcome of a transition with no output spec: nothing is deposited. */
export function emptyOutcome(): Outcome {
  return makeOutcome(new Map());
}

/**
 * The count `deposit` puts into its place, with a `drained` forward resolved by `drained(from)`.
 */
export function depositCount(deposit: Deposit, drained: (from: Place<any>) => number): number {
  return deposit.type === 'tokens' ? deposit.count : drained(deposit.from);
}

function sameDeposit(x: Deposit, y: Deposit): boolean {
  if (x.type === 'tokens') return y.type === 'tokens' && x.count === y.count;
  return y.type === 'drained' && x.from.name === y.from.name;
}

function sameOutcome(x: Outcome, y: Outcome): boolean {
  return x.deposits.length === y.deposits.length
    && x.deposits.every((d, i) => {
      const e = y.deposits[i]!;
      return d.place.name === e.place.name && sameDeposit(d.deposit, e.deposit);
    });
}

/**
 * The ways one firing of `t` can deposit (module docs). Never empty: a transition with no output
 * spec has the one empty outcome.
 */
export function outcomes(t: Transition): Outcome[] {
  if (t.outputSpec === null) return [emptyOutcome()];
  const result: Outcome[] = enumerateBranches(t.outputSpec).map(branch =>
    makeOutcome(new Map([...branch].map(p => [p.name, { place: p, deposit: ONE }]))));
  if (result.length === 0) result.push(emptyOutcome());
  // The executor takes the transition's first `Timeout` ([IO-013]), and so do we.
  if (t.actionTimeout !== null) {
    for (const deposits of timeoutDeposits(t.actionTimeout.child, t)) {
      const outcome = makeOutcome(deposits);
      if (!result.some(o => sameOutcome(o, outcome))) result.push(outcome);
    }
  }
  return result;
}

/**
 * A place the executor writes on timeout, and where the token comes from ([IO-013], [IO-014]).
 * `from` is the input a `ForwardInput` leaf copies (values unchanged, so each token keeps the
 * name it had there), or `null` for an `Out.place` leaf, whose unit token has no value and so no
 * ν name. The action writes nothing on that path, so the value is fixed by the spec alone.
 */
export interface TimeoutWrite {
  readonly to: string;
  readonly from: string | null;
}

/**
 * Every place the first `Timeout` of `t`'s output spec writes into, with where the token comes
 * from. Empty when the spec has no `Timeout`. The ν analyses read this to tell a timeout
 * deposit, which the executor makes by copying or by writing a unit token, from an action write,
 * which the ν contracts cover ([NU-010], [NU-051]).
 */
export function timeoutWrites(t: Transition): TimeoutWrite[] {
  const acc: TimeoutWrite[] = [];
  const walk = (out: Out): void => {
    switch (out.type) {
      case 'place': acc.push({ to: out.place.name, from: null }); break;
      case 'forward-input': acc.push({ to: out.to.name, from: out.from.name }); break;
      case 'timeout': walk(out.child); break;
      case 'xor':
      case 'and': for (const c of out.children) walk(c); break;
    }
  };
  if (t.actionTimeout !== null) walk(t.actionTimeout.child);
  return acc;
}

/**
 * The deposits of a `Timeout` child, one map per branch of it. The executors reject an `Xor`
 * under a `Timeout` when it fires; reading it as alternatives here keeps the enumeration total.
 */
function timeoutDeposits(out: Out, t: Transition): Map<string, OutcomeDeposit>[] {
  switch (out.type) {
    case 'place':
      return [new Map([[out.place.name, { place: out.place, deposit: ONE }]])];
    case 'forward-input': {
      const deposit = forwardDeposit(t, out.from);
      if (deposit.type === 'tokens' && deposit.count === 0) return [new Map()];
      return [new Map([[out.to.name, { place: out.to, deposit }]])];
    }
    case 'timeout':
      return timeoutDeposits(out.child, t);
    case 'xor':
      return out.children.flatMap(c => timeoutDeposits(c, t));
    case 'and': {
      let acc: Map<string, OutcomeDeposit>[] = [new Map()];
      for (const child of out.children) {
        const next = timeoutDeposits(child, t);
        acc = acc.flatMap(left => next.map(right => {
          const merged = new Map(left);
          for (const [name, d] of right) {
            // A place twice in one branch is rejected at build ([IO-011]); summing keeps
            // this total regardless.
            const prior = merged.get(name);
            merged.set(name, prior !== undefined && prior.deposit.type === 'tokens' && d.deposit.type === 'tokens'
              ? { place: d.place, deposit: { type: 'tokens', count: prior.deposit.count + d.deposit.count } }
              : d);
          }
          return merged;
        }));
      }
      return acc;
    }
  }
}

/**
 * What a timeout forward from `from` deposits ([IO-014]): one token per token the firing
 * consumed from `from`. A place that is not an input of `t` (the builder rejects it) consumes
 * nothing and forwards nothing.
 */
function forwardDeposit(t: Transition, from: Place<any>): Deposit {
  const spec = t.inputSpecs.find(s => s.place.name === from.name);
  if (spec === undefined) return { type: 'tokens', count: 0 };
  if (spec.type === 'one' || spec.type === 'exactly') return { type: 'tokens', count: requiredCount(spec) };
  return { type: 'drained', from: spec.place };
}

/** A timeout forward whose count the flat encodings cannot express ({@link drainedForward}). */
export interface DrainedForward {
  /** The transition declaring it. */
  readonly transition: string;
  /** The drained input place (`all` / `atLeast`). */
  readonly from: string;
  /** The place it forwards to. */
  readonly to: string;
}

/** The `unknown` reason the verifier gives for a net with this forward ([VER-003]). */
export function drainedForwardReason(forward: DrainedForward): string {
  return `transition '${forward.transition}' forwards its All/AtLeast input '${forward.from}' to '${forward.to}' `
    + 'on timeout, which deposits one token per token drained (IO-014), a marking-dependent count the flat '
    + 'encodings cannot express; refusing to certify on the linear routes (the state-space '
    + 'graphs decide it exactly: VER-017 enumeration, Route B)';
}

/**
 * The first timeout forward, in transition order, from an `all` / `atLeast` input: its deposit
 * is the drained batch, a transfer the incidence-matrix analyses (P-invariants, the linear
 * bound, the state equation, the firing bound, the CHC transition rule, Route A) have no column
 * for. The verifier lets the graph routes decide such a net and refuses it before the first
 * linear route.
 */
export function drainedForward(net: PetriNet): DrainedForward | null {
  for (const t of net.transitions) {
    for (const o of outcomes(t)) {
      for (const d of o.deposits) {
        if (d.deposit.type === 'drained') {
          return { transition: t.name, from: d.deposit.from.name, to: d.place.name };
        }
      }
    }
  }
  return null;
}
