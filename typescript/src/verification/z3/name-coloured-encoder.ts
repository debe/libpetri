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
 * minting, and a non-negative weighting of the flat places that weights every coloured
 * place at least one and that no flat row increases bounds the simultaneously-live names
 * to a finite `k` (`Σ_{coloured} M ≤ y·M0`; see {@link buildColouredPlan} and
 * {@link module:slot-bound-lp}, which takes the least such bound as a linear program). So
 * names are modelled as a **finite set of `k` colours**. Each coloured
 * place becomes `k` per-colour integer counts; a mint introduces a *globally
 * fresh* colour (one currently empty everywhere); a matched join consumes the
 * **same colour** from every correlated input, so no counterexample equates two
 * different names.
 *
 * The encoding reads two things it cannot check off the net. A declared mint
 * ({@link buildColouredPlan}'s `mintTransitions`: named by the caller, or consuming a
 * declared budget place) writes a freshly minted name ([NU-010]), and an EXTENDED coloured
 * consumer writes the name it consumed ([NU-051]). A `proven` is sound while those contracts
 * hold; the Lean development proves that inclusion (every run of the net is a run of the
 * encoding), not the converse.
 *
 * **Supported fragment**: {@link buildColouredPlan} returns `null` (and the
 * verifier falls back to the sound over-approximation) unless the net is in the
 * budget-bounded coloured fragment:
 * - coloured places = the correlated inputs of every matched transition, plus (in
 *   EXTENDED mode, [NU-051]) the declared carrier places and the joins' relay
 *   targets ([NU-054]);
 * - each coloured place is *produced only by* minting forks (count 1, no coloured
 *   input, a declared mint, no coloured write on timeout), EXTENDED relays (a timeout
 *   write only as a forward of the consumed input), or a matched join onto its
 *   declared relay targets (count 1, the join's shared colour), and *consumed only by*
 *   matched joins or EXTENDED coloured consumers — a relay threads one colour on, a
 *   drain drops it, each consuming exactly one coloured input at count 1;
 * - the coloured place set is structurally token-bounded: the colour-slot program of
 *   {@link module:slot-bound-lp} has an optimum, and its re-checked weighting bounds the
 *   simultaneously-live colour count by `k = ⌊y·M0⌋` (`Σ_{coloured} M ≤ y·M0`). A net
 *   whose program is infeasible (an unbounded colour leak) falls back, as does one
 *   whose weighting fails the re-check or that exceeds the program's limits;
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
 * consumer no resident colour) and the marking is not a sink state, mirroring the
 * flat {@link module:smt-encoder} deadlock. The encoding has no injection rule, so
 * the verifier never calls it with environment injection ([VER-006] AC7).
 *
 * Mirrors the Rust reference `name_coloured_encoder.rs` exactly and emits the same
 * SMT-LIB2 text byte for byte (VER-013).
 */
import type { PetriNet } from '../../core/petri-net.js';
import type { Place } from '../../core/place.js';
import { strandingExcuses, type ConditionalSinks } from '../rest-set.js';
import type { FlatNet } from '../encoding/flat-net.js';
import type { FlatTransition } from '../encoding/flat-transition.js';
import type { MarkingState } from '../marking-state.js';
import type { SmtProperty } from '../smt-property.js';
import type { PInvariant } from '../invariant/p-invariant.js';
import { checkedSlotBound, type LpAnswer, type SlotBound } from './slot-bound-lp.js';
import type { FragmentMode } from '../analysis/name-fragment.js';
import { timeoutWrites } from '../analysis/branch-outcomes.js';
import {
  countViolationCondition, indexOrdered, injectionMap, type SmtEncoding, strandedConditions,
} from './smt-encoder.js';

/** How a transition relates to the coloured (correlation-carrying) places. */
type Klass =
  | { readonly kind: 'mint'; readonly colouredOut: readonly number[] }
  /**
   * Matched join: consumes the shared colour from each `colouredIn` and, on this flat row's
   * branch, produces it once on each `relayOut` ([NU-054], EXTENDED only; empty otherwise).
   */
  | { readonly kind: 'join'; readonly colouredIn: readonly number[]; readonly relayOut: readonly number[] }
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
  /**
   * Colour-slot bound: the floor of the colour-slot program's optimum, re-checked
   * ({@link module:slot-bound-lp}), so at least the number of names live at once. It counts
   * coloured tokens rather than names, so it can exceed the initial budget, and it is `0`
   * when no coloured token can exist.
   */
  readonly k: number;
  /** Classification, one entry per flat transition (XOR branches included). */
  readonly classes: readonly Klass[];
  /** The net transitions read as mints, in net order ([NU-010]). */
  readonly mints: readonly string[];
  /** The net transitions whose rows relay a colour as coloured consumers ([NU-051]). */
  readonly relays: readonly string[];
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
 * `lp` solves the colour-slot program ({@link module:slot-bound-lp}) for the coloured places
 * it is given; the verifier passes `solveSlotBound` inside its `colour-slot bound` step. Its
 * answer is untrusted: `buildColouredPlan` takes `k` only from {@link checkedSlotBound}, which
 * re-checks the weighting against every flat row in exact arithmetic. `lp` is called once, and
 * only after every structural refusal has passed, none of which reads `k`. `onSlotBound`
 * receives the checked bound right after the check, before the `k = 0` refusal; the verifier
 * writes its report line there.
 *
 * `mintTransitions` names the transitions declared to mint ([NU-010]; see `declaredMints`
 * in `name-fragment`). A row that writes a coloured place without consuming one is a mint
 * only when its transition is named there, and never when the transition writes a coloured
 * place on timeout.
 */
export function buildColouredPlan(
  net: PetriNet,
  flat: FlatNet,
  initial: MarkingState,
  mintTransitions: ReadonlySet<string>,
  fragmentMode: FragmentMode,
  carrierPlaces: ReadonlySet<string>,
  lp: (coloured: readonly number[]) => LpAnswer,
  onSlotBound: (bound: SlotBound) => void = () => {},
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
    // NU-054: relay targets are coloured places, so the colour-slot bound below must
    // weight them too.
    for (const t of net.transitions) {
      for (const r of t.matchSpec?.relays ?? []) {
        const pid = flat.placeIndex.get(r.place.name);
        if (pid != null) isColoured[pid] = true;
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
  const mints: string[] = [];
  const relays: string[] = [];
  for (const ft of flat.transitions) {
    const t = ft.source;
    // What the executor itself writes into a coloured place on timeout ([IO-013], [IO-014]):
    // a copy of a consumed value, or a unit token with no name. A flat row does not say
    // whether the action or the timeout wrote it (equal outcomes share a row), so the rule
    // reads the source transition.
    const timeoutColoured = timeoutWrites(t).filter((w) => {
      const pid = flat.placeIndex.get(w.to);
      return pid != null && isColoured[pid]!;
    });
    const colouredIn = coloured.filter((pid) => ft.preVector[pid]! > 0);
    const colouredOut = coloured.filter((pid) => ft.postVector[pid]! > 0);
    const ms = ft.source.matchSpec;

    if (ms) {
      // Matched join: consumes coloured inputs (count 1), produces coloured places only as
      // declared relay targets (EXTENDED, [NU-054]), each at count 1.
      const relayNames = new Set<string>();
      if (fragmentMode === 'extended') for (const r of ms.relays) relayNames.add(r.place.name);
      if (colouredIn.length === 0) return null;
      if (colouredOut.some((pid) => !relayNames.has(flat.places[pid]!.name) || ft.postVector[pid]! !== 1)) return null;
      if (colouredIn.some((pid) => ft.preVector[pid]! !== 1)) return null;
      const keyPlaces = new Set(ms.keys.map((k) => k.place.name));
      // What the executor writes into a relay target on timeout is checked like an action's
      // write ([NU-054]): only a forward of a match key carries the join's colour. A unit token
      // has none and a forward of another input carries that input's, so such a firing fails
      // and deposits nothing, while this row would relay the colour.
      if (timeoutColoured.some((w) => w.from === null || !keyPlaces.has(w.from))) return null;
      // Every coloured input must be a key: an off-key one is taken FIFO at runtime,
      // whatever its colour, not the join's shared colour.
      if (colouredIn.some((pid) => !keyPlaces.has(flat.places[pid]!.name))) return null;
      classes.push({ kind: 'join', colouredIn, relayOut: colouredOut });
    } else if (colouredIn.length !== 0) {
      // EXTENDED coloured consumer (relay/drain, [NU-051]): a non-match transition
      // consuming a coloured place. Admitted only in EXTENDED mode, and only when it
      // consumes EXACTLY ONE coloured input at count EXACTLY ONE (higher counts would
      // over-count the name layer against the base marking's single token per place).
      // It relays the name into its coloured outputs (each at count 1) or drains it.
      if (fragmentMode !== 'extended') return null;
      if (colouredIn.length !== 1 || ft.preVector[colouredIn[0]!]! !== 1) return null;
      if (colouredOut.some((o) => ft.postVector[o]! !== 1)) return null;
      // A timeout deposit relays the consumed colour only when it forwards the coloured input
      // itself ([NU-051]): a forward of another input copies a name this row did not consume,
      // and a unit token has none.
      const inputName = flat.places[colouredIn[0]!]!.name;
      if (timeoutColoured.some((w) => w.from !== inputName)) return null;
      if (colouredOut.length !== 0 && !relays.includes(t.name)) relays.push(t.name);
      classes.push({ kind: 'consume', inputCol: colouredIn[0]!, colouredOut });
    } else if (colouredOut.length !== 0) {
      // Minting fork: produces coloured (count 1), consumes none, and is a declared mint
      // (named by the caller, or consuming a declared budget place). The declaration is what
      // states the mint contract of [NU-010]: the action writes a name freshly minted by
      // `freshName()`. Nothing in the net tells a mint from an action that copies a live
      // correlation id. (Boundedness is decided by the colour-slot bound below, not here.)
      if (colouredOut.some((o) => ft.postVector[o]! !== 1)) return null;
      if (!mintTransitions.has(t.name)) return null;
      // What the executor writes on timeout is never fresh, declared or not.
      if (timeoutColoured.length > 0) return null;
      if (!mints.includes(t.name)) mints.push(t.name);
      classes.push({ kind: 'mint', colouredOut });
    } else {
      // Touches no coloured place at all.
      classes.push({ kind: 'untouched' });
    }
  }

  // Colour-slot bound k, computed last: the simplex is the expensive step, and every
  // refusal above is independent of k.
  //
  // A colour is live iff some coloured place holds it, so `#live colours ≤
  // Σ_{coloured} M(p) ≤ y·M0` for any weighting `y ≥ 0` with `y_p ≥ 1` on the coloured
  // places that no flat row increases. `k` is the floor of the least such `y·M0`, the
  // optimum of the slot-bound program; any `k ≥ #live` is sound, since a mint may take any
  // free slot behind the freshness guard. The weighting is re-checked against every flat row
  // before `k` is read (`checkedSlotBound`, Lean `colourSlotBoundLP`). An infeasible program
  // means the coloured set is not structurally token-bounded (a genuine colour leak), so fall
  // back to the sound over-approximation, as on any other answer without a re-checked
  // weighting.
  const bound = checkedSlotBound(flat, initial, coloured, lp(coloured));
  onSlotBound(bound);
  if (bound.type !== 'bound') return null;
  const k = bound.k;
  // NU-053 AC6: `k = 0` is an exact plan — no coloured token can ever exist, so every
  // mint / join / consumer is dead and the zero-slot encoding emits no rule for them
  // (`SlotBound.lean`, `vacuous_colour_layer_lp`). The one shape it cannot encode is a net
  // with no uncoloured place at all (`Reachable` would be nullary and every rule's
  // `ForAll` binder list empty); such a net holds no token at M0, so fall back.
  if (k === 0 && coloured.length === P) return null;

  return { coloured, isColoured, k, classes, mints, relays };
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
 *
 * The encoding has no injection rule, so a `flat` with non-empty environment injection
 * yields an unsound relaxed predicate; the verifier never passes one ([VER-006] AC7).
 */
export function encodeColoured(
  plan: ColouredPlan,
  flat: FlatNet,
  initial: MarkingState,
  property: SmtProperty,
  invariants: readonly PInvariant[],
  sinkPlaces: ReadonlySet<Place<any>>,
  conditionalSinks: readonly ConditionalSinks[] = [],
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
              // A key that is also a relay target (a correlated self-loop) nets to zero:
              // guarded above, column copied unchanged.
              if (!cls.relayOut.includes(ip)) upd.push({ col, expr: `(- ${lay.cur[col]} 1)` });
            }
            // NU-054: colour c relayed once onto each relay target of this branch.
            for (const o of cls.relayOut) {
              if (cls.colouredIn.includes(o)) continue;
              const col = lay.colCol[o]![c]!;
              upd.push({ col, expr: `(+ ${lay.cur[col]} 1)` });
            }
          }));
        }
        break;
      case 'consume': {
        // One rule per colour: consume colour c from the single coloured input and
        // thread it into each coloured output (relay), or into none (drain). A relay back
        // into its own input (a self-loop) nets to zero, as a join's key that is also a
        // relay target does: the column keeps its `>= 1` guard and is carried over
        // unchanged. encodeRule keeps one update per column, so writing `- 1` and then
        // `+ 1` would leave only the `+ 1`.
        const selfLoop = cls.colouredOut.includes(cls.inputCol);
        for (let c = 0; c < k; c++) {
          lines.push(encodeRule(plan, lay, invariants, (enab, upd) => {
            uncolouredIncidence(lay, plan, ft, enab, upd);
            const icol = lay.colCol[cls.inputCol]![c]!;
            enab.push(`(>= ${lay.cur[icol]} 1)`);
            if (!selfLoop) upd.push({ col: icol, expr: `(- ${lay.cur[icol]} 1)` });
            for (const o of cls.colouredOut) {
              if (o === cls.inputCol) continue;
              const ocol = lay.colCol[o]![c]!;
              upd.push({ col: ocol, expr: `(+ ${lay.cur[ocol]} 1)` });
            }
          }));
        }
        break;
      }
    }
  }
  lines.push('');

  // Error rule. `null` ⇒ the property names an unresolved place; refuse to build a
  // vacuously-provable encoding and let the verifier report Unknown.
  const error = encodeError(plan, lay, flat, property, sinkPlaces, injectionMap(flat), conditionalSinks);
  if (error == null) return null;
  lines.push(error);
  lines.push('');
  lines.push('(assert (not Error))');
  lines.push('(check-sat)');

  return { smt2: lines.join('\n'), placeCount: P, counterCount: 0 };
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
  // copied unchanged. Each column is updated at most once: a second write would replace the
  // first rather than add to it, so every caller nets a self-loop out before pushing.
  const changed: (string | null)[] = new Array<string | null>(lay.cur.length).fill(null);
  for (const u of upd) {
    if (changed[u.col] != null) throw new Error(`column ${u.col} updated twice in one rule`);
    changed[u.col] = u.expr;
  }
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
  conditionalSinks: readonly ConditionalSinks[],
): string | null {
  const violation = encodeViolation(plan, lay, flat, property, sinkPlaces, envInj, conditionalSinks);
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
  conditionalSinks: readonly ConditionalSinks[],
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
    // DeadlockFree (VER-002): quiescent AND some marked place is not where resting
    // is permitted (VER-014). Mirrors the flat encoder's `stranded` disjunction over
    // the aggregate (all-colour) count of each place.
    case 'deadlock-free': {
      const conds = encodeColouredQuiescent(plan, lay, flat, envInj);
      if (conds == null) return 'false';
      const counts: string[] = [];
      for (let pid = 0; pid < flat.places.length; pid++) counts.push(aggregate(plan, lay, pid, lay.cur));
      const stranded = strandedConditions(strandingExcuses(flat, sinkPlaces, conditionalSinks), counts);
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
    // QuiescentCount (VER-002): the flat encoder's count clause over aggregate counts.
    case 'quiescent-count': {
      const bad = countViolationCondition(
        indexOrdered(flat, property.places).map((pid) => aggregate(plan, lay, pid, lay.cur)),
        indexOrdered(flat, property.waivedBy).map((pid) => aggregate(plan, lay, pid, lay.cur)),
        property.min,
        property.max,
      );
      if (bad == null) return 'false';
      const conds = encodeColouredQuiescent(plan, lay, flat, envInj);
      if (conds == null) return 'false';
      conds.push(bad);
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
 * Colour-aware quiescence predicate (NU-053): every transition that is not
 * reapable is disabled (no colour enables it). A reapable transition contributes
 * no clause, since a late executor reaps it and rests with it enabled (VER-002
 * reap-quiescence, TIME-013). Mirrors the flat `encodeQuiescent` with the same
 * env-injection relaxation (VER-006), lifted to the coloured layout. Carries no
 * sink clause; each property conjoins its own.
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
    // Reap-quiescence ([VER-002], [TIME-013]), as the flat encoder.
    if (ft.reapable) continue;
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
