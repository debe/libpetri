/**
 * @module name-coloured-encoder
 *
 * Bounded **name-coloured** CHC encoding for ν-net join correlation
 * ([NU-050] #1, Route A — the EUF-style carve-out).
 *
 * The flat {@link module:smt-encoder} is a pure *counting* abstraction: a place
 * is one integer, and a matched (ν-join) transition is encoded name-blind — it
 * fires whenever the input *counts* allow, regardless of whether the consumed
 * tokens actually share a correlation name. That over-approximation is sound for
 * `proven` on reachability-safety bounds but can report a **spurious** `violated`
 * whose counterexample silently equates two *distinct* names.
 *
 * This encoder removes that imprecision for the bounded fragment. The
 * decidability lever ([NU-040]) is a bounded live-name count: a budget place gates
 * minting, and a non-negative **P-semiflow** weighting every coloured place bounds
 * the simultaneously-live names to a finite `k` (`Σ_{coloured} M ≤ y·M0`; see
 * {@link buildColouredPlan} / `colourSlotBound`). So names are modelled as a
 * **finite set of `k` colours**. Each coloured
 * place becomes `k` per-colour integer counts; a mint introduces a *globally
 * fresh* colour (one currently empty everywhere); a matched join consumes the
 * **same colour** from every correlated input. Within the budget bound the
 * encoding is *exact* — sound and complete — so no different-name counterexample
 * survives.
 *
 * **Supported fragment**: {@link buildColouredPlan} returns `null` (and the
 * verifier falls back to the sound over-approximation) unless the net is in the
 * budget-bounded coloured fragment:
 * - coloured places = the correlated inputs of every matched transition, plus (in
 *   EXTENDED mode, [NU-051]) the declared carrier places;
 * - each coloured place is *produced only by* minting forks (count 1, no coloured
 *   input, costs ≥1 budget token) or EXTENDED relays, and *consumed only by*
 *   matched joins or EXTENDED coloured consumers — a relay threads one colour on, a
 *   drain drops it, each consuming exactly one coloured input at count 1;
 * - the coloured place set is structurally token-bounded: some non-negative
 *   P-semiflow weights every coloured place, so the simultaneously-live colour count
 *   is bounded by that semiflow's initial value `k` (`Σ_{coloured} M ≤ y·M0`). A net
 *   with no covering non-negative semiflow (an unbounded colour leak) falls back;
 * - coloured places start empty; no inhibitor/read/reset/consume-all arc touches a
 *   coloured place.
 *
 * XOR output branches are supported ([NU-053], Part 3): each branch is a separate
 * flat row classified by its own incidence, with `matchSpec` read from its source.
 *
 * **Properties**: reachability-safety properties compare aggregate coloured place
 * counts. Quiescence properties (`deadlock-free`, `joined-or-dead-lettered`) use a
 * colour-aware deadlock predicate ([NU-053], Part 2): every transition is disabled
 * for every colour (a mint has no globally-fresh colour, a join no shared colour, a
 * consumer no resident colour) and the marking is not a sink state — mirroring the
 * flat {@link module:smt-encoder} deadlock with the same env-injection relaxation.
 *
 * Mirrors the Rust reference `name_coloured_encoder.rs` exactly; the difference
 * is that this builds z3-solver expressions rather than emitting SMT-LIB2 text.
 * Z3 types are partially untyped; the ctx/fp parameters use `any`.
 */
import type { Arith, Bool, FuncDecl } from 'z3-solver';
import type { PetriNet } from '../../core/petri-net.js';
import type { Place } from '../../core/place.js';
import type { FlatNet } from '../encoding/flat-net.js';
import type { FlatTransition } from '../encoding/flat-transition.js';
import type { MarkingState } from '../marking-state.js';
import type { SmtProperty } from '../smt-property.js';
import type { PInvariant } from '../invariant/p-invariant.js';
import type { FragmentMode } from '../analysis/name-fragment.js';
import type { EncodingResult } from './smt-encoder.js';
import { flatNetIndexOf } from '../encoding/flat-net.js';

/** Z3 high-level context. Typed as `any` because z3-solver's TS types are incomplete. */
type Z3Context = any;
/** Z3 Fixedpoint solver instance. Typed as `any` because z3-solver's TS types are incomplete. */
type Z3Fixedpoint = any;

/** How a transition relates to the coloured (correlation-carrying) places. */
type Klass =
  | { readonly kind: 'mint'; readonly colouredOut: readonly number[] }
  | { readonly kind: 'join'; readonly colouredIn: readonly number[] }
  /**
   * EXTENDED coloured consumer ([NU-051]): a non-match transition that consumes
   * one same-coloured token from `inputCol` (count 1) and threads it into each
   * `colouredOut` (relay) or into none (drain — `colouredOut` empty).
   */
  | { readonly kind: 'consume'; readonly inputCol: number; readonly colouredOut: readonly number[] }
  | { readonly kind: 'untouched' };

/** A validated plan for the name-coloured encoding of a budget-bounded ν-net. */
export interface ColouredPlan {
  /** Flat indices of the coloured places (ascending). */
  readonly coloured: readonly number[];
  /** Per flat place: whether it is coloured. */
  readonly isColoured: readonly boolean[];
  /** Colour bound — the number of simultaneously-live names (the P-semiflow slot bound). */
  readonly k: number;
  /** Classification, one entry per flat transition (XOR branches included). */
  readonly classes: readonly Klass[];
}

/**
 * Sound colour-slot bound `k`: a colour is live iff some coloured place holds it, so
 * `#live colours ≤ Σ_{coloured} M(p) ≤ y·M0` for any non-negative P-semiflow `y`
 * (`y·C = 0`, `y ≥ 0`) that weights every coloured place `≥ 1`. Returns the tightest
 * such `y·M0` (each `PInvariant.constant` is `y·M0`), or `null` when no covering
 * non-negative semiflow exists — the coloured set is then not structurally
 * token-bounded (a genuine unbounded colour leak) and the caller must fall back.
 *
 * `0` is a bound like any other (NU-053 AC6): with the covering law's initial sum at
 * zero no coloured token can ever exist, every mint / join / consumer is dead on the
 * reachable set, and the zero-slot plan is exact (`Semiflow.lean`,
 * `vacuous_colour_layer`). A validated semi-positive law's `y·M0` is never negative.
 *
 * Mirrors the Rust reference `colour_slot_bound`.
 */
function colourSlotBound(coloured: readonly number[], semiflows: readonly PInvariant[]): number | null {
  const w = (inv: PInvariant, pid: number): number => inv.weights[pid] ?? 0;
  const isSemiflow = (inv: PInvariant): boolean => inv.weights.every((x) => x >= 0);

  // Tightest bound: a single non-negative P-semiflow weighting every coloured place.
  let single: number | null = null;
  for (const inv of semiflows) {
    if (isSemiflow(inv) && coloured.every((pid) => w(inv, pid) >= 1)) {
      if (single === null || inv.constant < single) single = inv.constant;
    }
  }
  if (single !== null) return single;

  // Otherwise sum non-negative semiflows that touch a coloured place — the sum is
  // itself a valid non-negative P-semiflow, so `Σ y·M0` over any covering set is a
  // sound (looser) bound. Zero-constant semiflows cover their places for free, so they
  // go in first; a semiflow with a positive constant is added only if it touches a
  // coloured place the free ones left uncovered (decided against that snapshot, so the
  // result does not depend on enumeration order). If some coloured place stays at
  // weight 0 across all of them, no non-negative semiflow covers it, so the coloured
  // set is not structurally token-bounded → null (sound over-approximation).
  const covered = new Array<boolean>(coloured.length).fill(false);
  for (const inv of semiflows) {
    if (!isSemiflow(inv) || inv.constant !== 0) continue;
    for (let i = 0; i < coloured.length; i++) {
      if (w(inv, coloured[i]!) >= 1) covered[i] = true;
    }
  }
  const free = [...covered];
  let sumConst = 0;
  for (const inv of semiflows) {
    if (!isSemiflow(inv) || inv.constant === 0) continue;
    if (!coloured.some((pid, i) => !free[i] && w(inv, pid) >= 1)) continue;
    for (let i = 0; i < coloured.length; i++) {
      if (w(inv, coloured[i]!) >= 1) covered[i] = true;
    }
    sumConst += inv.constant;
  }
  if (covered.every((c) => c)) return sumConst;
  return null;
}

/**
 * Detects whether `net` is in the supported budget-bounded coloured fragment
 * (mint→matched-join, plus the EXTENDED coloured consumers and carrier places of
 * [NU-051], with XOR-expanded output branches) and, if so, returns the plan for
 * {@link encodeColoured}. Returns `null` otherwise — the verifier then uses the
 * sound over-approximation.
 *
 * Each flat row carries a back-reference to its source transition
 * ({@link FlatTransition.source}); an XOR transition expands to one flat row per
 * output branch (no 1:1 net↔flat assumption), so we read `matchSpec` from the
 * source while classifying by the flat row's own incidence.
 *
 * `semiflows` are the net's non-negative P-semiflows ({@link computePSemiflows}); a
 * covering one sets the colour-slot bound `k` (see {@link colourSlotBound}).
 */
export function buildColouredPlan(
  net: PetriNet,
  flat: FlatNet,
  initial: MarkingState,
  budgetNames: ReadonlySet<string>,
  fragmentMode: FragmentMode,
  carrierPlaces: ReadonlySet<string>,
  semiflows: readonly PInvariant[],
): ColouredPlan | null {
  const P = flat.places.length;

  // 1. Coloured places = every matched transition's correlated inputs, plus (in
  //    EXTENDED mode) the declared carrier places that thread a fork-minted name
  //    through intermediate places to a ν-join input ([NU-051]).
  const isColoured: boolean[] = new Array<boolean>(P).fill(false);
  for (const t of net.transitions) {
    const ms = t.matchSpec;
    if (ms) {
      for (const key of ms.keys) {
        const pid = flat.placeIndex.get(key.place.name);
        if (pid == null) return null;
        isColoured[pid] = true;
      }
    }
  }
  if (fragmentMode === 'extended') {
    for (const c of carrierPlaces) {
      const pid = flat.placeIndex.get(c);
      if (pid != null) isColoured[pid] = true;
    }
  }
  const coloured: number[] = [];
  for (let i = 0; i < P; i++) if (isColoured[i]) coloured.push(i);
  if (coloured.length === 0) return null;

  // Coloured places must start empty — no initial colour assignment is modelled.
  for (const pid of coloured) {
    if (initial.tokens(flat.places[pid]!) !== 0) return null;
  }

  // Colour-slot bound k: a colour is live iff some coloured place holds it, so
  // `#live colours ≤ Σ_{coloured} M(p) ≤ y·M0` for any non-negative P-semiflow `y`
  // weighting every coloured place `≥ 1`. `k` is the tightest such `y·M0`; any
  // `k ≥ #live` is sound — a larger k only costs O(k) columns, never
  // under-approximates, since a mint may take any free slot behind the freshness
  // guard. If no covering non-negative semiflow exists the coloured set is not
  // structurally token-bounded (a genuine unbounded colour leak), so fall back to the
  // sound over-approximation. This replaces the old budget-count `k` and both
  // structural discipline checks (atomic-rejoin + budget-Φ) below.
  const k = colourSlotBound(coloured, semiflows);
  if (k === null) return null;
  // NU-053 AC6: `k = 0` is an exact plan — no coloured token can ever exist, so every
  // mint / join / consumer is dead and the zero-slot encoding emits no rule for them
  // (`Semiflow.lean`, `vacuous_colour_layer`). The one shape it cannot encode is a net
  // with no uncoloured place at all (`Reachable` would be nullary and every rule's
  // `ForAll` binder list empty); such a net holds no token at M0, so fall back.
  if (k === 0 && coloured.length === P) return null;

  // Budget places gate minting: a mint must consume ≥1 budget token — that is what
  // makes it a fresh-name fork rather than an arbitrary coloured producer.
  const budgetIdx = new Set<number>();
  for (const n of budgetNames) {
    const i = flat.placeIndex.get(n);
    if (i != null) budgetIdx.add(i);
  }

  // No inhibitor/read/reset/consume-all arc may touch a coloured place.
  for (const ft of flat.transitions) {
    const touches =
      ft.inhibitorPlaces.some((i) => isColoured[i]) ||
      ft.readPlaces.some((i) => isColoured[i]) ||
      ft.resetPlaces.some((i) => isColoured[i]) ||
      ft.consumeAll.some((ca, i) => ca && isColoured[i]!);
    if (touches) return null;
  }

  // 2. Classify each flat row from its own incidence (matchSpec from its source).
  const classes: Klass[] = [];
  for (const ft of flat.transitions) {
    const colouredIn = coloured.filter((pid) => ft.preVector[pid]! > 0);
    const colouredOut = coloured.filter((pid) => ft.postVector[pid]! > 0);
    const ms = ft.source.matchSpec;

    if (ms) {
      // Matched join: consumes coloured inputs (count 1), produces none.
      if (colouredOut.length !== 0 || colouredIn.length === 0) return null;
      if (colouredIn.some((pid) => ft.preVector[pid]! !== 1)) return null;
      classes.push({ kind: 'join', colouredIn });
    } else if (colouredIn.length !== 0) {
      // EXTENDED coloured consumer (relay/drain, [NU-051]): a non-match transition
      // consuming a coloured place. Admitted only in EXTENDED mode, and only when it
      // consumes EXACTLY ONE coloured input at count EXACTLY ONE (higher counts would
      // over-count the name layer against the base marking's single token per place).
      // It relays the name into its coloured outputs (each at count 1) or drains it.
      if (fragmentMode !== 'extended') return null;
      if (colouredIn.length !== 1 || ft.preVector[colouredIn[0]!]! !== 1) return null;
      if (colouredOut.some((o) => ft.postVector[o]! !== 1)) return null;
      classes.push({ kind: 'consume', inputCol: colouredIn[0]!, colouredOut });
    } else if (colouredOut.length !== 0) {
      // Minting fork: produces coloured (count 1), consumes none, and must consume
      // ≥1 budget token — that is what makes it a fresh-name fork rather than an
      // arbitrary coloured producer. (Boundedness is decided by the colour-slot bound
      // above, not here.)
      if (colouredOut.some((o) => ft.postVector[o]! !== 1)) return null;
      let budgetConsumed = 0;
      for (const b of budgetIdx) budgetConsumed += ft.preVector[b]!;
      if (budgetConsumed < 1) return null;
      classes.push({ kind: 'mint', colouredOut });
    } else {
      // Touches no coloured place at all.
      classes.push({ kind: 'untouched' });
    }
  }

  return { coloured, isColoured, k, classes };
}

/**
 * Column layout over the coloured state vector: uncoloured place → one var,
 * coloured place → `k` per-colour vars. The current/next-marking variables are
 * named consts reused across every rule (each `ForAll` scopes its own binding).
 */
interface Layout {
  /** Column index of each uncoloured place (`-1` if coloured). */
  readonly colUnc: number[];
  /** Per coloured place: its `k` column indices (empty if uncoloured). */
  readonly colCol: number[][];
  /** Total column count. */
  readonly nCols: number;
  /** Current-marking vars, one per column. */
  readonly cur: Arith[];
  /** Next-marking vars, one per column. */
  readonly nxt: Arith[];
  /** The literal `0`: what a coloured place aggregates to when `k = 0`. */
  readonly zero: Arith;
}

function buildLayout(ctx: Z3Context, plan: ColouredPlan, P: number): Layout {
  const colUnc: number[] = new Array<number>(P).fill(-1);
  const colCol: number[][] = Array.from({ length: P }, () => []);
  let nCols = 0;
  for (let i = 0; i < P; i++) {
    if (plan.isColoured[i]) {
      const idxs: number[] = [];
      for (let c = 0; c < plan.k; c++) idxs.push(nCols++);
      colCol[i] = idxs;
    } else {
      colUnc[i] = nCols++;
    }
  }
  const cur: Arith[] = [];
  const nxt: Arith[] = [];
  for (let col = 0; col < nCols; col++) {
    cur.push(ctx.Int.const(`c${col}`));
    nxt.push(ctx.Int.const(`cp${col}`));
  }
  return { colUnc, colCol, nCols, cur, nxt, zero: ctx.Int.val(0) };
}

/** Contributes the enablement guards and the changed-column updates of a rule. */
type Fill = (enab: Bool[], upd: Map<number, Arith>) => void;

/**
 * Encodes the supported ν-net as bounded name-coloured CHC for Z3 Spacer. Reuses
 * {@link EncodingResult}; with the query `(not Error)`, `sat` ⇒ PROVEN, `unsat` ⇒
 * VIOLATED (the Spacer convention shared with the flat encoder).
 *
 * Returns `null` when the property names a place that does not resolve in the net
 * (see {@link encodeViolation}); the verifier reports Unknown rather than certify a
 * vacuous PROVEN.
 */
export function encodeColoured(
  ctx: Z3Context,
  fp: Z3Fixedpoint,
  plan: ColouredPlan,
  flat: FlatNet,
  initial: MarkingState,
  property: SmtProperty,
  invariants: readonly PInvariant[],
  sinkPlaces: ReadonlySet<Place<any>> = new Set(),
): EncodingResult | null {
  const P = flat.places.length;
  const k = plan.k;
  const lay = buildLayout(ctx, plan, P);

  const intSort = ctx.Int.sort();
  const boolSort = ctx.Bool.sort();
  const markingSorts: any[] = new Array(lay.nCols).fill(intSort);
  const reachable: FuncDecl = ctx.Function.declare('Reachable', ...markingSorts, boolSort);
  fp.registerRelation(reachable);
  const error: FuncDecl = ctx.Function.declare('Error', boolSort);
  fp.registerRelation(error);

  // Init: uncoloured places carry their initial count; coloured start empty.
  const initArgs: Arith[] = new Array(lay.nCols);
  for (let i = 0; i < P; i++) {
    if (plan.isColoured[i]) {
      for (let c = 0; c < k; c++) initArgs[lay.colCol[i]![c]!] = ctx.Int.val(0);
    } else {
      initArgs[lay.colUnc[i]!] = ctx.Int.val(initial.tokens(flat.places[i]!));
    }
  }
  fp.addRule((reachable as any).call(...initArgs) as Bool, 'init');

  // Transition rules.
  for (let ti = 0; ti < plan.classes.length; ti++) {
    const cls = plan.classes[ti]!;
    const ft = flat.transitions[ti]!;
    if (cls.kind === 'untouched') {
      addRule(ctx, fp, reachable, lay, plan, invariants, `${ft.name}_u`, (enab, upd) =>
        uncolouredIncidence(ctx, lay, plan, ft, enab, upd),
      );
    } else if (cls.kind === 'mint') {
      const colouredOut = cls.colouredOut;
      for (let c = 0; c < k; c++) {
        const cc = c;
        addRule(ctx, fp, reachable, lay, plan, invariants, `${ft.name}_mint_${cc}`, (enab, upd) => {
          uncolouredIncidence(ctx, lay, plan, ft, enab, upd);
          // Globally fresh colour: cc must be empty in every coloured place.
          for (const q of plan.coloured) enab.push(lay.cur[lay.colCol[q]![cc]!]!.eq(0));
          for (const o of colouredOut) {
            const col = lay.colCol[o]![cc]!;
            upd.set(col, lay.cur[col]!.add(1));
          }
        });
      }
    } else if (cls.kind === 'join') {
      const colouredIn = cls.colouredIn;
      for (let c = 0; c < k; c++) {
        const cc = c;
        addRule(ctx, fp, reachable, lay, plan, invariants, `${ft.name}_join_${cc}`, (enab, upd) => {
          uncolouredIncidence(ctx, lay, plan, ft, enab, upd);
          // Same colour cc present in every correlated input.
          for (const ip of colouredIn) {
            const col = lay.colCol[ip]![cc]!;
            enab.push(lay.cur[col]!.ge(1));
            upd.set(col, lay.cur[col]!.add(-1));
          }
        });
      }
    } else {
      // EXTENDED coloured consumer: one rule per colour — consume colour cc from
      // the single coloured input and thread it into each coloured output (relay),
      // or into none (drain).
      const inputCol = cls.inputCol;
      const colouredOut = cls.colouredOut;
      for (let c = 0; c < k; c++) {
        const cc = c;
        addRule(ctx, fp, reachable, lay, plan, invariants, `${ft.name}_consume_${cc}`, (enab, upd) => {
          uncolouredIncidence(ctx, lay, plan, ft, enab, upd);
          const icol = lay.colCol[inputCol]![cc]!;
          enab.push(lay.cur[icol]!.ge(1));
          upd.set(icol, lay.cur[icol]!.add(-1));
          for (const o of colouredOut) {
            const ocol = lay.colCol[o]![cc]!;
            upd.set(ocol, lay.cur[ocol]!.add(1));
          }
        });
      }
    }
  }

  // Error rule. `false` ⇒ the property names an unresolved place; refuse to build
  // a vacuously-provable encoding and let the verifier report Unknown.
  if (!addErrorRule(ctx, fp, reachable, error, lay, plan, flat, property, sinkPlaces)) {
    return null;
  }

  return {
    errorExpr: (error as any).call() as Bool,
    reachableDecl: reachable,
  };
}

/**
 * Builds one transition CHC rule. `fill` contributes the enablement guards and
 * the changed-column updates; every other column is copied unchanged, changed
 * columns get a non-negativity guard, and the (lifted) P-invariants constrain the
 * successor.
 */
function addRule(
  ctx: Z3Context,
  fp: Z3Fixedpoint,
  reachable: FuncDecl,
  lay: Layout,
  plan: ColouredPlan,
  invariants: readonly PInvariant[],
  ruleName: string,
  fill: Fill,
): void {
  const enab: Bool[] = [];
  const upd = new Map<number, Arith>();
  fill(enab, upd);

  const conds: Bool[] = [(reachable as any).call(...lay.cur) as Bool, ...enab];
  for (let col = 0; col < lay.nCols; col++) {
    const expr = upd.get(col);
    if (expr !== undefined) {
      conds.push(lay.nxt[col]!.eq(expr), lay.nxt[col]!.ge(0));
    } else {
      conds.push(lay.nxt[col]!.eq(lay.cur[col]!));
    }
  }
  for (const inv of invariants) {
    const eq = liftedInvariant(ctx, inv, plan, lay, lay.nxt);
    if (eq) conds.push(eq);
  }

  const body = ctx.And(...conds);
  const head = (reachable as any).call(...lay.nxt) as Bool;
  const qRule = ctx.ForAll([...lay.cur, ...lay.nxt], ctx.Implies(body, head));
  fp.addRule(qRule, ruleName);
}

/**
 * Pushes the enablement guards and column updates contributed by a transition's
 * **uncoloured** incidence (consume/produce on non-coloured places). Coloured
 * columns are handled by the caller (mint produces, join consumes). Mirrors the
 * Rust reference — no blanket current-marking non-negativity guard.
 */
function uncolouredIncidence(
  ctx: Z3Context,
  lay: Layout,
  plan: ColouredPlan,
  ft: FlatTransition,
  enab: Bool[],
  upd: Map<number, Arith>,
): void {
  const P = ft.preVector.length;
  for (let i = 0; i < P; i++) {
    if (plan.isColoured[i]) continue;
    const col = lay.colUnc[i]!;
    const pre = ft.preVector[i]!;
    if (pre > 0) enab.push(lay.cur[col]!.ge(pre));
    if (ft.resetPlaces.includes(i) || ft.consumeAll[i]) {
      upd.set(col, ctx.Int.val(ft.postVector[i]!));
    } else {
      const delta = ft.postVector[i]! - ft.preVector[i]!;
      if (delta !== 0) upd.set(col, lay.cur[col]!.add(delta));
    }
  }
  // Inhibitor / read arcs (all on uncoloured places — checked in buildColouredPlan).
  for (const pid of ft.inhibitorPlaces) enab.push(lay.cur[lay.colUnc[pid]!]!.eq(0));
  for (const pid of ft.readPlaces) enab.push(lay.cur[lay.colUnc[pid]!]!.ge(1));
}

/**
 * Aggregate token-count expression for a place over the given var-set: the single
 * uncoloured var, or the sum of its colours.
 */
function aggregate(plan: ColouredPlan, lay: Layout, place: number, vars: readonly Arith[]): Arith {
  if (plan.isColoured[place]) {
    const cols = lay.colCol[place]!;
    // k = 0: a coloured place has no slot and never holds a token.
    if (cols.length === 0) return lay.zero;
    let sum = vars[cols[0]!]!;
    for (let c = 1; c < cols.length; c++) sum = sum.add(vars[cols[c]!]!);
    return sum;
  }
  return vars[lay.colUnc[place]!]!;
}

/**
 * Lifts a flat P-invariant to the coloured layout: a coloured place's variable
 * becomes the sum of its colours (= its aggregate count), so the (true) flat
 * invariant constrains the coloured successor without excluding any reachable
 * state.
 */
function liftedInvariant(
  ctx: Z3Context,
  inv: PInvariant,
  plan: ColouredPlan,
  lay: Layout,
  vars: readonly Arith[],
): Bool | null {
  if (inv.support.size === 0) return null;
  let sum: Arith = ctx.Int.val(0);
  for (const i of inv.support) {
    const agg = aggregate(plan, lay, i, vars);
    const w = inv.weights[i]!;
    sum = sum.add(w === 1 ? agg : agg.mul(w));
  }
  return sum.eq(inv.constant);
}

/**
 * Encodes the error rule: a reachable marking that violates the property.
 * Returns `false` when the property names an unresolved place ({@link encodeViolation}
 * returned `null`); no rule is added and the caller reports Unknown rather than
 * certify a vacuous PROVEN.
 */
function addErrorRule(
  ctx: Z3Context,
  fp: Z3Fixedpoint,
  reachable: FuncDecl,
  error: FuncDecl,
  lay: Layout,
  plan: ColouredPlan,
  flat: FlatNet,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
): boolean {
  const violation = encodeViolation(ctx, plan, lay, flat, property, lay.cur, sinkPlaces);
  if (violation === null) return false; // unresolved property place → signal Unknown
  const reachBody = (reachable as any).call(...lay.cur) as Bool;
  const body = ctx.And(reachBody, violation);
  const head = (error as any).call() as Bool;
  const qRule = ctx.ForAll([...lay.cur], ctx.Implies(body, head));
  fp.addRule(qRule, 'error');
  return true;
}

/**
 * Encodes the property-violation condition over the coloured current marking.
 * Reachability-safety properties compare aggregate place counts; quiescence
 * properties ([NU-053]) use the colour-aware deadlock predicate.
 *
 * Returns `null` when the property names a place that does not resolve in the
 * net (e.g. a typo'd bound/pending place). A `false` violation term there would
 * make the Error rule unsatisfiable and yield a **vacuous** PROVEN, silently
 * certifying a mis-named place; `null` propagates up so the verifier reports
 * Unknown instead.
 */
function encodeViolation(
  ctx: Z3Context,
  plan: ColouredPlan,
  lay: Layout,
  flat: FlatNet,
  property: SmtProperty,
  cur: readonly Arith[],
  sinkPlaces: ReadonlySet<Place<any>>,
): Bool | null {
  switch (property.type) {
    case 'place-bound':
    case 'branch-place-bound': {
      const idx = flatNetIndexOf(flat, property.place);
      if (idx < 0) return null;
      return aggregate(plan, lay, idx, cur).gt(property.bound);
    }
    case 'mutual-exclusion': {
      const i1 = flatNetIndexOf(flat, property.p1);
      const i2 = flatNetIndexOf(flat, property.p2);
      if (i1 < 0 || i2 < 0) return ctx.Bool.val(false);
      return ctx.And(aggregate(plan, lay, i1, cur).ge(1), aggregate(plan, lay, i2, cur).ge(1));
    }
    case 'unreachable': {
      const conds: Bool[] = [];
      for (const place of property.places) {
        const idx = flatNetIndexOf(flat, place);
        if (idx >= 0) conds.push(aggregate(plan, lay, idx, cur).ge(1));
      }
      if (conds.length === 0) return ctx.Bool.val(false);
      return conds.length === 1 ? conds[0]! : ctx.And(...conds);
    }
    case 'deadlock-free':
      return encodeColouredDeadlock(ctx, plan, lay, flat, sinkPlaces);
    case 'joined-or-dead-lettered': {
      const idx = flatNetIndexOf(flat, property.pending);
      if (idx < 0) return null;
      const deadlock = encodeColouredDeadlock(ctx, plan, lay, flat, sinkPlaces);
      return ctx.And(deadlock, aggregate(plan, lay, idx, cur).ge(1));
    }
  }
}

/** Conjunction of `xs` (empty ⇒ `true`), avoiding variadic-spread edge cases. */
function andAll(ctx: Z3Context, xs: Bool[]): Bool {
  if (xs.length === 0) return ctx.Bool.val(true);
  let r = xs[0]!;
  for (let i = 1; i < xs.length; i++) r = ctx.And(r, xs[i]!);
  return r;
}

/** Disjunction of `xs` (empty ⇒ `false`). */
function orAll(ctx: Z3Context, xs: Bool[]): Bool {
  if (xs.length === 0) return ctx.Bool.val(false);
  let r = xs[0]!;
  for (let i = 1; i < xs.length; i++) r = ctx.Or(r, xs[i]!);
  return r;
}

/** Maps injected environment-place index -> injection bound (null = unbounded). */
function injectedEnvIndices(flat: FlatNet): Map<number, number | null> {
  const out = new Map<number, number | null>();
  for (const [name, bound] of flat.environmentInjection) {
    const idx = flat.placeIndex.get(name);
    if (idx != null) out.set(idx, bound);
  }
  return out;
}

/**
 * The uncoloured disable reasons for a flat row: marking-dependent clauses (any one
 * true ⇒ the transition's uncoloured part is unmet), plus a flag that it is
 * permanently disabled (an env cap below the demand means it can never fire).
 * Coloured places are excluded — their enablement is the per-class colour term.
 * Mirrors the flat {@link module:smt-encoder} deadlock with the same env relaxation.
 */
function uncolouredDisable(
  ft: FlatTransition,
  lay: Layout,
  plan: ColouredPlan,
  envInj: Map<number, number | null>,
): { reasons: Bool[]; permanentlyDisabled: boolean } {
  const reasons: Bool[] = [];
  let permanentlyDisabled = false;
  const P = ft.preVector.length;
  for (let i = 0; i < P; i++) {
    if (plan.isColoured[i] || ft.preVector[i]! === 0) continue;
    if (envInj.has(i)) {
      const bound = envInj.get(i)!;
      if (bound !== null && ft.preVector[i]! > bound) permanentlyDisabled = true;
      continue;
    }
    reasons.push(lay.cur[lay.colUnc[i]!]!.lt(ft.preVector[i]!));
  }
  for (const inh of ft.inhibitorPlaces) {
    reasons.push(lay.cur[lay.colUnc[inh]!]!.gt(0));
  }
  for (const rd of ft.readPlaces) {
    if (envInj.has(rd)) {
      const bound = envInj.get(rd)!;
      if (bound !== null && bound < 1) permanentlyDisabled = true;
      continue;
    }
    reasons.push(lay.cur[lay.colUnc[rd]!]!.lt(1));
  }
  return { reasons, permanentlyDisabled };
}

/**
 * The colour-specific "disabled for every colour" term for a class (`null` if the
 * class imposes no coloured enablement constraint). Combined by the caller with the
 * uncoloured disable reasons: the transition is disabled if EITHER holds.
 */
function colouredDisabledTerm(ctx: Z3Context, cls: Klass, plan: ColouredPlan, lay: Layout): Bool | null {
  const k = plan.k;
  switch (cls.kind) {
    case 'untouched':
      return null;
    case 'mint': {
      // No globally-fresh colour: for every colour c, some coloured place holds c.
      const perColour: Bool[] = [];
      for (let c = 0; c < k; c++) {
        const present = plan.coloured.map((q) => lay.cur[lay.colCol[q]![c]!]!.ge(1));
        perColour.push(orAll(ctx, present));
      }
      return andAll(ctx, perColour);
    }
    case 'join': {
      // No colour is shared by all correlated inputs: for every colour c, some
      // input lacks c.
      const perColour: Bool[] = [];
      for (let c = 0; c < k; c++) {
        const missing = cls.colouredIn.map((i) => lay.cur[lay.colCol[i]![c]!]!.eq(0));
        perColour.push(orAll(ctx, missing));
      }
      return andAll(ctx, perColour);
    }
    case 'consume': {
      // No colour present at the single coloured input.
      const perColour: Bool[] = [];
      for (let c = 0; c < k; c++) {
        perColour.push(lay.cur[lay.colCol[cls.inputCol]![c]!]!.eq(0));
      }
      return andAll(ctx, perColour);
    }
  }
}

/**
 * Colour-aware deadlock predicate ([NU-053]): every transition is disabled (no
 * colour enables it) and the marking is not a sink state. Mirrors the flat
 * {@link module:smt-encoder}'s `encodeDeadlock` with the same env-injection
 * relaxation (VER-006), lifted to the coloured layout.
 */
function encodeColouredDeadlock(
  ctx: Z3Context,
  plan: ColouredPlan,
  lay: Layout,
  flat: FlatNet,
  sinkPlaces: ReadonlySet<Place<any>>,
): Bool {
  const envInj = injectedEnvIndices(flat);
  const disabledConditions: Bool[] = [];
  for (let ti = 0; ti < plan.classes.length; ti++) {
    const cls = plan.classes[ti]!;
    const ft = flat.transitions[ti]!;
    const { reasons, permanentlyDisabled } = uncolouredDisable(ft, lay, plan, envInj);
    if (permanentlyDisabled) {
      // The transition can never fire — it is always "disabled".
      disabledConditions.push(ctx.Bool.val(true));
      continue;
    }
    const term = colouredDisabledTerm(ctx, cls, plan, lay);
    if (term !== null) reasons.push(term);
    if (reasons.length === 0) {
      // Always enabled (possibly via injection) — no marking is a deadlock.
      return ctx.Bool.val(false);
    }
    disabledConditions.push(reasons.length === 1 ? reasons[0]! : orAll(ctx, reasons));
  }

  // Not a sink state: some non-sink place still holds a token (aggregate count).
  const sinkIndices = new Set<number>();
  for (const sink of sinkPlaces) {
    const idx = flatNetIndexOf(flat, sink);
    if (idx >= 0) sinkIndices.add(idx);
  }
  if (sinkIndices.size > 0) {
    const nonSink: Bool[] = [];
    for (let pid = 0; pid < flat.places.length; pid++) {
      if (sinkIndices.has(pid)) continue;
      nonSink.push(aggregate(plan, lay, pid, lay.cur).ge(1));
    }
    if (nonSink.length > 0) {
      disabledConditions.push(orAll(ctx, nonSink));
    }
  }

  return andAll(ctx, disabledConditions);
}
