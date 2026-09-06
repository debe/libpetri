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
 * counts. Quiescence properties (`deadlock-free`, `terminates-at-sink`,
 * `joined-or-dead-lettered`) use a
 * colour-aware deadlock predicate ([NU-053], Part 2): every transition is disabled
 * for every colour (a mint has no globally-fresh colour, a join no shared colour, a
 * consumer no resident colour) and the marking is not a sink state — mirroring the
 * flat {@link module:smt-encoder} deadlock with the same env-injection relaxation.
 *
 * Mirrors the Rust reference `name_coloured_encoder.rs` exactly and emits the same
 * SMT-LIB2 text byte for byte (VER-013).
 */
import type { PetriNet } from '../../core/petri-net.js';
import type { Place } from '../../core/place.js';
import type { FlatNet } from '../encoding/flat-net.js';
import type { FlatTransition } from '../encoding/flat-transition.js';
import type { MarkingState } from '../marking-state.js';
import type { SmtProperty } from '../smt-property.js';
import type { PInvariant } from '../invariant/p-invariant.js';
import type { FragmentMode } from '../analysis/name-fragment.js';
import { indexOrdered, injectionMap, type SmtEncoding } from './smt-encoder.js';

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
 * coloured place → `k` per-colour vars, named exactly as the Rust reference names
 * them (`m{i}` / `m{i}_{c}`, next marking with a `p` suffix).
 */
interface Layout {
  /** Column index of each uncoloured place (`-1` if coloured). */
  readonly colUnc: number[];
  /** Per coloured place: its `k` column indices (empty if uncoloured). */
  readonly colCol: number[][];
  /** Current-marking variable names, one per column. */
  readonly cur: string[];
  /** Next-marking variable names, one per column. */
  readonly nxt: string[];
}

function buildLayout(plan: ColouredPlan, P: number): Layout {
  const colUnc: number[] = new Array<number>(P).fill(-1);
  const colCol: number[][] = Array.from({ length: P }, () => []);
  const cur: string[] = [];
  const nxt: string[] = [];
  for (let i = 0; i < P; i++) {
    if (plan.isColoured[i]) {
      const idxs: number[] = [];
      for (let c = 0; c < plan.k; c++) {
        idxs.push(cur.length);
        cur.push(`m${i}_${c}`);
        nxt.push(`m${i}_${c}p`);
      }
      colCol[i] = idxs;
    } else {
      colUnc[i] = cur.length;
      cur.push(`m${i}`);
      nxt.push(`m${i}p`);
    }
  }
  return { colUnc, colCol, cur, nxt };
}

function quantified(names: readonly string[]): string {
  return names.map((v) => `(${v} Int)`).join(' ');
}

/** A changed column and its update expression. */
interface Update {
  readonly col: number;
  readonly expr: string;
}

/** Contributes the enablement guards and the changed-column updates of a rule. */
type Fill = (enab: string[], upd: Update[]) => void;

/**
 * Encodes the supported ν-net as bounded name-coloured CHC for Z3 Spacer, as SMT-LIB2
 * text byte-identical to the Rust reference (`encode_coloured`). With the query
 * `(not Error)`, `sat` ⇒ PROVEN, `unsat` ⇒ VIOLATED (the Spacer convention shared with
 * the flat encoder).
 *
 * Returns `null` when the property names a place that does not resolve in the net
 * (see {@link encodeViolation}); the verifier reports Unknown rather than certify a
 * vacuous PROVEN.
 */
export function encodeColoured(
  plan: ColouredPlan,
  flat: FlatNet,
  initial: MarkingState,
  property: SmtProperty,
  invariants: readonly PInvariant[],
  sinkPlaces: ReadonlySet<Place<any>>,
): SmtEncoding | null {
  const P = flat.places.length;
  const k = plan.k;
  const lay = buildLayout(plan, P);
  const nCols = lay.cur.length;

  const lines: string[] = [];
  lines.push('(set-logic HORN)');
  lines.push('');
  lines.push(`(declare-fun Reachable (${new Array<string>(nCols).fill('Int').join(' ')}) Bool)`);
  lines.push('(declare-fun Error () Bool)');
  lines.push('');

  // Init: uncoloured places carry their initial count; coloured start empty.
  const init: string[] = [];
  for (let i = 0; i < P; i++) {
    if (plan.isColoured[i]) {
      for (let c = 0; c < k; c++) init.push('0');
    } else {
      init.push(String(initial.tokens(flat.places[i]!)));
    }
  }
  lines.push(`(assert (Reachable ${init.join(' ')}))`);
  lines.push('');

  // Transition rules.
  for (let ti = 0; ti < plan.classes.length; ti++) {
    const cls = plan.classes[ti]!;
    const ft = flat.transitions[ti]!;
    switch (cls.kind) {
      case 'untouched':
        lines.push(encodeRule(plan, lay, invariants, (enab, upd) => uncolouredIncidence(lay, plan, ft, enab, upd)));
        break;
      case 'mint':
        for (let c = 0; c < k; c++) {
          lines.push(encodeRule(plan, lay, invariants, (enab, upd) => {
            uncolouredIncidence(lay, plan, ft, enab, upd);
            // Globally fresh colour: c must be empty in every coloured place.
            for (const q of plan.coloured) enab.push(`(= ${lay.cur[lay.colCol[q]![c]!]} 0)`);
            for (const o of cls.colouredOut) {
              const col = lay.colCol[o]![c]!;
              upd.push({ col, expr: `(+ ${lay.cur[col]} 1)` });
            }
          }));
        }
        break;
      case 'join':
        for (let c = 0; c < k; c++) {
          lines.push(encodeRule(plan, lay, invariants, (enab, upd) => {
            uncolouredIncidence(lay, plan, ft, enab, upd);
            // Same colour c present in every correlated input.
            for (const ip of cls.colouredIn) {
              const col = lay.colCol[ip]![c]!;
              enab.push(`(>= ${lay.cur[col]} 1)`);
              upd.push({ col, expr: `(- ${lay.cur[col]} 1)` });
            }
          }));
        }
        break;
      case 'consume':
        // One rule per colour: consume colour c from the single coloured input and
        // thread it into each coloured output (relay), or into none (drain).
        for (let c = 0; c < k; c++) {
          lines.push(encodeRule(plan, lay, invariants, (enab, upd) => {
            uncolouredIncidence(lay, plan, ft, enab, upd);
            const icol = lay.colCol[cls.inputCol]![c]!;
            enab.push(`(>= ${lay.cur[icol]} 1)`);
            upd.push({ col: icol, expr: `(- ${lay.cur[icol]} 1)` });
            for (const o of cls.colouredOut) {
              const ocol = lay.colCol[o]![c]!;
              upd.push({ col: ocol, expr: `(+ ${lay.cur[ocol]} 1)` });
            }
          }));
        }
        break;
    }
  }
  lines.push('');

  // Error rule. `null` ⇒ the property names an unresolved place; refuse to build a
  // vacuously-provable encoding and let the verifier report Unknown.
  const error = encodeError(plan, lay, flat, property, sinkPlaces, injectionMap(flat));
  if (error == null) return null;
  lines.push(error);
  lines.push('');
  lines.push('(assert (not Error))');
  lines.push('(check-sat)');

  return { smt2: lines.join('\n'), placeCount: P };
}

/**
 * Builds one transition CHC rule. `fill` contributes the enablement guards and the
 * changed-column updates; every other column is copied unchanged, changed columns get
 * a non-negativity guard, and the (lifted) P-invariants constrain the successor.
 */
function encodeRule(plan: ColouredPlan, lay: Layout, invariants: readonly PInvariant[], fill: Fill): string {
  const enab: string[] = [];
  const upd: Update[] = [];
  fill(enab, upd);

  const conditions: string[] = [`(Reachable ${lay.cur.join(' ')})`, ...enab];

  // A changed column gets its update + non-negativity guard; every other column is
  // copied unchanged. A later update of the same column wins.
  const changed: (string | null)[] = new Array<string | null>(lay.cur.length).fill(null);
  for (const u of upd) changed[u.col] = u.expr;
  for (let col = 0; col < lay.cur.length; col++) {
    const expr = changed[col];
    if (expr != null) {
      conditions.push(`(= ${lay.nxt[col]} ${expr})`);
      conditions.push(`(>= ${lay.nxt[col]} 0)`);
    } else {
      conditions.push(`(= ${lay.nxt[col]} ${lay.cur[col]})`);
    }
  }

  for (const inv of invariants) {
    const eq = liftedInvariant(inv, plan, lay, lay.nxt);
    if (eq != null) conditions.push(eq);
  }

  const body = `(and ${conditions.join('\n            ')})`;
  return `(assert (forall (${quantified([...lay.cur, ...lay.nxt])})\n  (=> ${body}\n      (Reachable ${lay.nxt.join(' ')}))))`;
}

/**
 * Pushes the enablement guards and column updates contributed by a transition's
 * **uncoloured** incidence (consume/produce on non-coloured places). Coloured columns
 * are handled by the caller (mint produces, join/consumer consume).
 */
function uncolouredIncidence(lay: Layout, plan: ColouredPlan, ft: FlatTransition, enab: string[], upd: Update[]): void {
  const P = ft.preVector.length;
  for (let i = 0; i < P; i++) {
    if (plan.isColoured[i]) continue;
    const col = lay.colUnc[i]!;
    const pre = ft.preVector[i]!;
    if (pre > 0) enab.push(`(>= ${lay.cur[col]} ${pre})`);
    if (ft.resetPlaces.includes(i) || ft.consumeAll[i]) {
      upd.push({ col, expr: String(ft.postVector[i]) });
    } else {
      const delta = ft.postVector[i]! - ft.preVector[i]!;
      if (delta > 0) upd.push({ col, expr: `(+ ${lay.cur[col]} ${delta})` });
      else if (delta < 0) upd.push({ col, expr: `(- ${lay.cur[col]} ${-delta})` });
    }
  }
  // Inhibitor / read arcs (all on uncoloured places — checked in buildColouredPlan).
  for (const pid of ft.inhibitorPlaces) enab.push(`(= ${lay.cur[lay.colUnc[pid]!]} 0)`);
  for (const pid of ft.readPlaces) enab.push(`(>= ${lay.cur[lay.colUnc[pid]!]} 1)`);
}

/**
 * Aggregate token-count expression for a place over the given var-set (`cur` or
 * `nxt`): the single uncoloured var, or the sum of its colours.
 */
function aggregate(plan: ColouredPlan, lay: Layout, place: number, names: readonly string[]): string {
  if (plan.isColoured[place]) {
    const cols = lay.colCol[place]!;
    // k = 0: a coloured place has no slot and never holds a token.
    if (cols.length === 0) return '0';
    if (cols.length === 1) return names[cols[0]!]!;
    return `(+ ${cols.map((c) => names[c]!).join(' ')})`;
  }
  return names[lay.colUnc[place]!]!;
}

/**
 * Lifts a flat P-invariant to the coloured layout: a coloured place's variable
 * becomes the sum of its colours (= its aggregate count). Returns `null` when the
 * invariant support is empty.
 */
function liftedInvariant(inv: PInvariant, plan: ColouredPlan, lay: Layout, names: readonly string[]): string | null {
  const terms: string[] = [];
  for (const i of [...inv.support].sort((a, b) => a - b)) {
    const agg = aggregate(plan, lay, i, names);
    const w = inv.weights[i]!;
    terms.push(w === 1 ? agg : `(* ${w} ${agg})`);
  }
  if (terms.length === 0) return null;
  const sum = terms.length === 1 ? terms[0]! : `(+ ${terms.join(' ')})`;
  return `(= ${sum} ${inv.constant})`;
}

/**
 * Encodes the error rule: a reachable marking that violates the property, or `null`
 * when the property names an unresolved place ({@link encodeViolation}).
 */
function encodeError(
  plan: ColouredPlan,
  lay: Layout,
  flat: FlatNet,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  envInj: ReadonlyMap<number, number | null>,
): string | null {
  const violation = encodeViolation(plan, lay, flat, property, sinkPlaces, envInj);
  if (violation == null) return null;
  return `(assert (forall (${quantified(lay.cur)})\n  (=> (and (Reachable ${lay.cur.join(' ')}) ${violation})\n      Error)))`;
}

/**
 * Encodes the property-violation condition over the coloured current marking.
 * Reachability-safety properties compare aggregate place counts; quiescence
 * properties (NU-053) build on the colour-aware quiescence predicate, each
 * conjoining its own clause.
 *
 * Returns `null` when the property names a place that does not resolve in the net
 * (e.g. a typo'd bound/pending place). A `false` violation term there would make the
 * Error rule unsatisfiable and yield a **vacuous** PROVEN, silently certifying a
 * mis-named place; `null` propagates up so the verifier reports Unknown instead.
 */
function encodeViolation(
  plan: ColouredPlan,
  lay: Layout,
  flat: FlatNet,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  envInj: ReadonlyMap<number, number | null>,
): string | null {
  const anyPlacePresent = (places: Iterable<Place<any>>): string => {
    const conds = indexOrdered(flat, places).map((pid) => `(>= ${aggregate(plan, lay, pid, lay.cur)} 1)`);
    return conds.length === 0 ? 'false' : `(and ${conds.join(' ')})`;
  };
  switch (property.type) {
    case 'place-bound':
    case 'branch-place-bound': {
      const pid = flat.placeIndex.get(property.place.name);
      // Unresolved bound place: a false violation term would vacuously PROVE the
      // bound. Return null so the verifier reports Unknown instead of certifying.
      if (pid == null) return null;
      return `(> ${aggregate(plan, lay, pid, lay.cur)} ${property.bound})`;
    }
    case 'mutual-exclusion':
      return anyPlacePresent([property.p1, property.p2]);
    case 'unreachable':
      return anyPlacePresent(property.places);
    // DeadlockFree (VER-002): quiescent AND some marked place is not a declared
    // sink. Mirrors the flat encoder's `stranded` disjunction.
    case 'deadlock-free': {
      const conds = encodeColouredQuiescent(plan, lay, flat, envInj);
      if (conds == null) return 'false';
      const sinks = new Set(indexOrdered(flat, sinkPlaces));
      const stranded: string[] = [];
      for (let pid = 0; pid < flat.places.length; pid++) {
        if (!sinks.has(pid)) stranded.push(`(>= ${aggregate(plan, lay, pid, lay.cur)} 1)`);
      }
      // Every place is a declared sink: nothing can ever be stranded.
      if (stranded.length === 0) return 'false';
      conds.push(`(or ${stranded.join(' ')})`);
      return joinColoured(conds);
    }
    // TerminatesAtSink (VER-002): quiescent AND no declared sink marked.
    case 'terminates-at-sink': {
      const conds = encodeColouredQuiescent(plan, lay, flat, envInj);
      if (conds == null) return 'false';
      for (const pid of indexOrdered(flat, sinkPlaces)) {
        conds.push(`(= ${aggregate(plan, lay, pid, lay.cur)} 0)`);
      }
      return joinColoured(conds);
    }
    // JoinedOrDeadLettered (NU-040 AC4): quiescent AND `pending` marked, with NO
    // sink clause.
    case 'joined-or-dead-lettered': {
      const pid = flat.placeIndex.get(property.pending.name);
      if (pid == null) return null;
      const conds = encodeColouredQuiescent(plan, lay, flat, envInj);
      if (conds == null) return 'false';
      conds.push(`(>= ${aggregate(plan, lay, pid, lay.cur)} 1)`);
      return joinColoured(conds);
    }
  }
}

/**
 * The uncoloured disable reasons for a flat row: marking-dependent clauses (any one
 * true ⇒ the transition's uncoloured part is unmet), collected into `reasons`;
 * returns `true` when the transition is permanently disabled (an env cap below the
 * demand means it can never fire). Coloured places are excluded — their enablement is
 * the per-class colour term.
 */
function uncolouredDisable(
  ft: FlatTransition,
  lay: Layout,
  plan: ColouredPlan,
  envInj: ReadonlyMap<number, number | null>,
  reasons: string[],
): boolean {
  let permanentlyDisabled = false;
  const P = ft.preVector.length;
  for (let i = 0; i < P; i++) {
    if (plan.isColoured[i] || ft.preVector[i] === 0) continue;
    if (envInj.has(i)) {
      const bound = envInj.get(i)!;
      if (bound != null && ft.preVector[i]! > bound) permanentlyDisabled = true;
      continue;
    }
    reasons.push(`(< ${lay.cur[lay.colUnc[i]!]} ${ft.preVector[i]})`);
  }
  for (const inh of ft.inhibitorPlaces) reasons.push(`(> ${lay.cur[lay.colUnc[inh]!]} 0)`);
  for (const rd of ft.readPlaces) {
    if (envInj.has(rd)) {
      const bound = envInj.get(rd)!;
      if (bound != null && bound < 1) permanentlyDisabled = true;
      continue;
    }
    reasons.push(`(< ${lay.cur[lay.colUnc[rd]!]} 1)`);
  }
  return permanentlyDisabled;
}

/**
 * The colour-specific "disabled for every colour" term for a class (`null` if the
 * class imposes no coloured enablement constraint). Combined by the caller with the
 * uncoloured disable reasons: the transition is disabled if EITHER holds.
 */
function colouredDisabledTerm(cls: Klass, plan: ColouredPlan, lay: Layout): string | null {
  const k = plan.k;
  if (k === 0) {
    // k = 0 (NU-053 AC6): no colour can ever be present, so every coloured class is
    // disabled outright; the empty conjunctions below would render as `(and )`.
    return cls.kind === 'untouched' ? null : 'true';
  }
  switch (cls.kind) {
    case 'untouched':
      return null;
    case 'mint': {
      // No globally-fresh colour: for every colour c, some coloured place holds c.
      const perColour: string[] = [];
      for (let c = 0; c < k; c++) {
        const present = plan.coloured.map((q) => `(>= ${lay.cur[lay.colCol[q]![c]!]} 1)`);
        perColour.push(`(or ${present.join(' ')})`);
      }
      return `(and ${perColour.join(' ')})`;
    }
    case 'join': {
      // No colour is shared by all correlated inputs: for every colour c, some input
      // lacks c.
      const perColour: string[] = [];
      for (let c = 0; c < k; c++) {
        const missing = cls.colouredIn.map((i) => `(= ${lay.cur[lay.colCol[i]![c]!]} 0)`);
        perColour.push(`(or ${missing.join(' ')})`);
      }
      return `(and ${perColour.join(' ')})`;
    }
    case 'consume': {
      // No colour present at the single coloured input.
      const perColour: string[] = [];
      for (let c = 0; c < k; c++) perColour.push(`(= ${lay.cur[lay.colCol[cls.inputCol]![c]!]} 0)`);
      return `(and ${perColour.join(' ')})`;
    }
  }
}

/** Joins coloured violation conjuncts. Empty is vacuously true. */
function joinColoured(conds: readonly string[]): string {
  return conds.length === 0 ? 'true' : `(and ${conds.join(' ')})`;
}

/**
 * Colour-aware quiescence predicate (NU-053): every transition is disabled (no
 * colour enables it). Mirrors the flat `encodeQuiescent` with the same
 * env-injection relaxation (VER-006), lifted to the coloured layout. Carries no
 * sink clause — each property conjoins its own.
 *
 * `null` means some transition is enabled in every marking: never quiescent.
 */
function encodeColouredQuiescent(
  plan: ColouredPlan,
  lay: Layout,
  flat: FlatNet,
  envInj: ReadonlyMap<number, number | null>,
): string[] | null {
  const disabledConditions: string[] = [];
  for (let ti = 0; ti < plan.classes.length; ti++) {
    const cls = plan.classes[ti]!;
    const ft = flat.transitions[ti]!;
    const reasons: string[] = [];
    const permanentlyDisabled = uncolouredDisable(ft, lay, plan, envInj, reasons);
    if (permanentlyDisabled) {
      // The transition can never fire — it is always "disabled".
      disabledConditions.push('true');
      continue;
    }
    const term = colouredDisabledTerm(cls, plan, lay);
    if (term != null) reasons.push(term);
    // Always enabled (possibly via injection) — never quiescent.
    if (reasons.length === 0) return null;
    disabledConditions.push(reasons.length === 1 ? reasons[0]! : `(or ${reasons.join(' ')})`);
  }

  return disabledConditions;
}
