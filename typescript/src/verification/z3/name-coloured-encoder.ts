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
 * decidability lever ([NU-040]) is the budget: with a `Budget` place pre-seeded
 * with `k` tokens gating every mint, at most `k` correlation names are live at
 * once. So names are modelled as a **finite set of `k` colours**. Each coloured
 * place becomes `k` per-colour integer counts; a mint introduces a *globally
 * fresh* colour (one currently empty everywhere); a matched join consumes the
 * **same colour** from every correlated input. Within the budget bound the
 * encoding is *exact* — sound and complete — so no different-name counterexample
 * survives.
 *
 * **Supported fragment (tracer bullet)**: {@link buildColouredPlan} returns
 * `null` (and the verifier falls back to the sound over-approximation) unless the
 * net is in the simple **mint → matched-join** shape: coloured places = the
 * correlated inputs of every matched transition; each is produced only by minting
 * forks (count 1, no coloured input, costs ≥1 budget token) and consumed only by
 * matched joins (count 1, produces no coloured token); budget consumed only by
 * mints and produced only by joins (so live colours ≤ initial budget = `k`);
 * coloured places start empty; no inhibitor/read/reset/consume-all arc touches a
 * coloured place; no XOR output anywhere.
 *
 * Mirrors the Rust reference `name_coloured_encoder.rs` exactly; the difference
 * is that this builds z3-solver expressions rather than emitting SMT-LIB2 text.
 * Z3 types are partially untyped; the ctx/fp parameters use `any`.
 */
import type { Arith, Bool, FuncDecl } from 'z3-solver';
import type { PetriNet } from '../../core/petri-net.js';
import type { FlatNet } from '../encoding/flat-net.js';
import type { FlatTransition } from '../encoding/flat-transition.js';
import type { MarkingState } from '../marking-state.js';
import type { SmtProperty } from '../smt-property.js';
import type { PInvariant } from '../invariant/p-invariant.js';
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
  | { readonly kind: 'untouched' };

/** A validated plan for the name-coloured encoding of a budget-bounded ν-net. */
export interface ColouredPlan {
  /** Flat indices of the coloured places (ascending). */
  readonly coloured: readonly number[];
  /** Per flat place: whether it is coloured. */
  readonly isColoured: readonly boolean[];
  /** Colour bound — the number of simultaneously-live names (= initial budget). */
  readonly k: number;
  /** Classification per flat transition (1:1 — the fragment forbids XOR). */
  readonly classes: readonly Klass[];
}

/**
 * Detects whether `net` is in the supported budget-bounded mint→matched-join
 * fragment and, if so, returns the plan for {@link encodeColoured}. Returns
 * `null` otherwise — the verifier then uses the sound over-approximation.
 */
export function buildColouredPlan(
  net: PetriNet,
  flat: FlatNet,
  initial: MarkingState,
  budgetNames: ReadonlySet<string>,
): ColouredPlan | null {
  const P = flat.places.length;

  // No XOR: every original transition maps 1:1 to a flat row.
  if (flat.transitions.length !== [...net.transitions].length) {
    return null;
  }

  // 1. Coloured places = union of every matched transition's correlated inputs.
  //    Read the match spec off each flat row's source transition.
  const isColoured: boolean[] = new Array<boolean>(P).fill(false);
  for (const ft of flat.transitions) {
    const ms = ft.source.matchSpec;
    if (ms) {
      for (const key of ms.keys) {
        const pid = flat.placeIndex.get(key.place.name);
        if (pid == null) return null;
        isColoured[pid] = true;
      }
    }
  }
  const coloured: number[] = [];
  for (let i = 0; i < P; i++) if (isColoured[i]) coloured.push(i);
  if (coloured.length === 0) return null;

  // Coloured places must start empty — no initial colour assignment is modelled.
  for (const pid of coloured) {
    if (initial.tokens(flat.places[pid]!) !== 0) return null;
  }

  // Colour bound k = total initial budget tokens (the live-name ceiling).
  const budgetIdx = new Set<number>();
  for (const n of budgetNames) {
    const i = flat.placeIndex.get(n);
    if (i != null) budgetIdx.add(i);
  }
  if (budgetIdx.size === 0) return null;
  let k = 0;
  for (const b of budgetIdx) k += initial.tokens(flat.places[b]!);
  if (k === 0) return null;

  // No inhibitor/read/reset/consume-all arc may touch a coloured place.
  for (const ft of flat.transitions) {
    const touches =
      ft.inhibitorPlaces.some((i) => isColoured[i]) ||
      ft.readPlaces.some((i) => isColoured[i]) ||
      ft.resetPlaces.some((i) => isColoured[i]) ||
      ft.consumeAll.some((ca, i) => ca && isColoured[i]!);
    if (touches) return null;
  }

  // 2. Classify each transition from its flat incidence.
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
    } else if (colouredOut.length !== 0) {
      // Minting fork: produces coloured (count 1), consumes none, costs budget.
      if (colouredIn.length !== 0) return null;
      if (colouredOut.some((o) => ft.postVector[o]! !== 1)) return null;
      let budgetConsumed = 0;
      for (const b of budgetIdx) budgetConsumed += ft.preVector[b]!;
      if (budgetConsumed < 1) return null;
      classes.push({ kind: 'mint', colouredOut });
    } else {
      // Touches no coloured place at all.
      if (colouredIn.length !== 0) return null;
      classes.push({ kind: 'untouched' });
    }
  }

  // 3. Budget discipline: consumed only by mints, produced only by joins, AND
  //    conserved — a join may not refund MORE budget than the cheapest mint
  //    consumes, else repeated mint→join cycles inflate the pool above k, the real
  //    net can hold > k simultaneously-live names, and the k-colour encoding would
  //    UNDER-approximate and report a false `Proven`. With this bound live colours
  //    ≤ initial budget = k. Fail-closed (return null → sound over-approx) otherwise.
  let minMintCost: number | null = null;
  let maxJoinRefund = 0;
  for (let ti = 0; ti < classes.length; ti++) {
    const cls = classes[ti]!;
    const ft = flat.transitions[ti]!;
    for (const b of budgetIdx) {
      if (ft.preVector[b]! > 0 && cls.kind !== 'mint') return null;
      if (ft.postVector[b]! > 0 && cls.kind !== 'join') return null;
    }
    if (cls.kind === 'mint') {
      let cost = 0;
      for (const b of budgetIdx) cost += ft.preVector[b]!;
      minMintCost = minMintCost === null ? cost : Math.min(minMintCost, cost);
    } else if (cls.kind === 'join') {
      let refund = 0;
      for (const b of budgetIdx) refund += ft.postVector[b]!;
      maxJoinRefund = Math.max(maxJoinRefund, refund);
    }
  }
  if (minMintCost === null || maxJoinRefund > minMintCost) return null;

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
  return { colUnc, colCol, nCols, cur, nxt };
}

/** Contributes the enablement guards and the changed-column updates of a rule. */
type Fill = (enab: Bool[], upd: Map<number, Arith>) => void;

/**
 * Encodes the supported ν-net as bounded name-coloured CHC for Z3 Spacer. Reuses
 * {@link EncodingResult}; with the query `(not Error)`, `sat` ⇒ PROVEN, `unsat` ⇒
 * VIOLATED (the Spacer convention shared with the flat encoder).
 */
export function encodeColoured(
  ctx: Z3Context,
  fp: Z3Fixedpoint,
  plan: ColouredPlan,
  flat: FlatNet,
  initial: MarkingState,
  property: SmtProperty,
  invariants: readonly PInvariant[],
): EncodingResult {
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
    } else {
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
    }
  }

  // Error rule.
  addErrorRule(ctx, fp, reachable, error, lay, plan, flat, property);

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

/** Encodes the error rule: a reachable marking that violates the property. */
function addErrorRule(
  ctx: Z3Context,
  fp: Z3Fixedpoint,
  reachable: FuncDecl,
  error: FuncDecl,
  lay: Layout,
  plan: ColouredPlan,
  flat: FlatNet,
  property: SmtProperty,
): void {
  const reachBody = (reachable as any).call(...lay.cur) as Bool;
  const violation = encodeViolation(ctx, plan, lay, flat, property, lay.cur);
  const body = ctx.And(reachBody, violation);
  const head = (error as any).call() as Bool;
  const qRule = ctx.ForAll([...lay.cur], ctx.Implies(body, head));
  fp.addRule(qRule, 'error');
}

/**
 * Encodes the property-violation condition over the coloured current marking.
 * Only reachability-safety properties are routed here (the verifier guarantees
 * it); quiescence properties yield `false` (no violating state).
 */
function encodeViolation(
  ctx: Z3Context,
  plan: ColouredPlan,
  lay: Layout,
  flat: FlatNet,
  property: SmtProperty,
  cur: readonly Arith[],
): Bool {
  switch (property.type) {
    case 'place-bound':
    case 'branch-place-bound': {
      const idx = flatNetIndexOf(flat, property.place);
      if (idx < 0) return ctx.Bool.val(false);
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
    // Quiescence properties are never routed here.
    case 'deadlock-free':
    case 'joined-or-dead-lettered':
      return ctx.Bool.val(false);
  }
}
