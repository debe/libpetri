import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, type Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { andPlaces, outPlace } from '../../src/core/out.js';
import { matchKey, matchSpec, relayKey } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { produces } from './producing-actions.js';

/**
 * PNID literature nets as libpetri ν-nets, copied from the validation study in
 * `research/net-metrics/validation/pnid/src/nets.ts` (van der Werf, Rivkin, Montali,
 * Polyvyanyy, "Correctness Notions for Petri Nets with Identifiers", Fund. Inf. 190, 2024).
 * Structure only: every output-declaring transition gets a producing action, none is executed.
 */

/** One transition row: name, consumed inputs, produced outputs, match keys, relay targets, read arcs. */
type Row = readonly [
  string, readonly string[], readonly string[], { match?: string[]; relay?: string[]; read?: string[] }?,
];

/** A net from rows; `places` returns each place object by name (one object per name). */
export function pnidNet(name: string, rows: readonly Row[]): { net: PetriNet; places: Map<string, Place<unknown>> } {
  const places = new Map<string, Place<unknown>>();
  const p = (n: string): Place<unknown> => {
    let x = places.get(n);
    if (x === undefined) {
      x = place<unknown>(n);
      places.set(n, x);
    }
    return x;
  };
  const key = (q: Place<unknown>) => matchKey(q, (v: unknown) => nameId(String(v)));
  const relay = (q: Place<unknown>) => relayKey(q, (v: unknown) => nameId(String(v)));
  const b = PetriNet.builder(name);
  for (const [t, ins, outs, opts] of rows) {
    let tb = Transition.builder(t).inputs(...ins.map(n => one(p(n))));
    if (outs.length > 0) {
      tb = tb.outputs(outs.length === 1 ? outPlace(p(outs[0]!)) : andPlaces(...outs.map(p))).action(produces());
    }
    if (opts?.match) {
      tb = tb.match(matchSpec(...opts.match.map(n => key(p(n))), ...(opts.relay ?? []).map(n => relay(p(n)))));
    }
    for (const r of opts?.read ?? []) tb = tb.read(p(r));
    b.transition(tb.build());
  }
  return { net: b.build(), places };
}

/**
 * P Fig. 11(b), "violates resource exclusive assignment": `create_order` reads a clerk and mints
 * an order name onto `order` and `order_clerk`; `send_order` joins the two by name. The clerk is
 * only read, so orders are minted without bound: Route B never closes. With 2 clerks,
 * `placeBound(order_clerk, 2)` is violated at depth 3 (three `create_order`).
 */
export const FIG_11B_ROWS: readonly Row[] = [
  ['create_order', [], ['order', 'order_clerk'], { read: ['clerk'] }],
  ['send_order', ['order', 'order_clerk'], ['send_done'], { match: ['order', 'order_clerk'] }],
];

/** P Fig. 11(c), the budget pattern: the clerk is consumed at create and returned at send. */
export const FIG_11C_ROWS: readonly Row[] = [
  ['create_order', ['clerk'], ['order', 'order_clerk']],
  ['send_order', ['order', 'order_clerk'], ['clerk'], { match: ['order', 'order_clerk'] }],
];

/**
 * P Fig. 13(b), the O-resource closure: `a` mints a case onto `P1` and the assignment `OR`, `b`
 * relays `P1` into `B1` and `B2`, and the joins `c` / `d` each need the one `OR` token, refunding
 * `R`. The second branch of every case is stuck forever, so `B2` grows past the live cases once
 * `R` is refunded. EXTENDED fragment with carrier `P1`; in BASE, `b` reads as a fresh mint and
 * the joins never fire.
 */
export const FIG_13B_ROWS: readonly Row[] = [
  ['a', ['R'], ['P1', 'OR']],
  ['b', ['P1'], ['B1', 'B2']],
  ['c', ['B1', 'OR'], ['R'], { match: ['B1', 'OR'] }],
  ['d', ['B2', 'OR'], ['R'], { match: ['B2', 'OR'] }],
];

/** P Fig. 12(a): fork `b` of a relayed case, two branches `c` / `d`, joined again by `e`. */
export const FIG_12A_ROWS: readonly Row[] = [
  ['a', ['SUPPLY'], ['P1']],
  ['b', ['P1'], ['B1', 'B2']],
  ['c', ['B1'], ['C1']],
  ['d', ['B2'], ['D1']],
  ['e', ['C1', 'D1'], ['E'], { match: ['C1', 'D1'] }],
];

/** Drops every relay declaration: the same net as the analysers saw it before NU-054. */
export function withoutRelays(rows: readonly Row[]): Row[] {
  return rows.map(([t, ins, outs, opts]) => {
    if (opts?.relay === undefined) return [t, ins, outs, opts] as Row;
    const { relay: _dropped, ...rest } = opts;
    return [t, ins, outs, rest] as Row;
  });
}

/**
 * P Fig. 12(c), resource closure 2: `a` mints a case onto `P1` and the assignment `OR`, `b`
 * forks it, `c` / `d` relay the branches, the ν-join `e` rejoins them onto `P5` — a relay target
 * (NU-054), since `P5` is a key of the `f` / `g` joins — and both `f` and `g` refund `R`.
 * Research nets `closure2`; carriers P1, B1, B2, C1, D1; budget R. Paper: identifier sound,
 * conservative, bounded.
 */
export const FIG_12C_ROWS: readonly Row[] = [
  ['a', ['R'], ['P1', 'OR']],
  ['b', ['P1'], ['B1', 'B2']],
  ['c', ['B1'], ['C1']],
  ['d', ['B2'], ['D1']],
  ['e', ['C1', 'D1'], ['P5'], { match: ['C1', 'D1'], relay: ['P5'] }],
  ['f', ['P5', 'OR'], ['R'], { match: ['P5', 'OR'] }],
  ['g', ['P5', 'OR'], ['R'], { match: ['P5', 'OR'] }],
];

/**
 * P Fig. 6(a) N1, correlated (research nets `n1Corr`): `A` co-mints one case name onto `Y1` and
 * `p`; the join `B` writes it back onto its own key `Y1` and onto `w`, `q`; `C` moves `Y1` to
 * `Y2`; the join `D` writes back onto its key `Y2` and onto `r`; `E` collects. Budget SUPPLY, no
 * carriers. NU-054 test derivation: `deadlockFree` is violated with the trace `A, C`.
 */
export const N1_CORR_ROWS: readonly Row[] = [
  ['A', ['SUPPLY'], ['Y1', 'p']],
  ['B', ['p', 'Y1'], ['Y1', 'w', 'q'], { match: ['p', 'Y1'], relay: ['Y1', 'w', 'q'] }],
  ['C', ['Y1'], ['Y2']],
  ['D', ['q', 'w', 'Y2'], ['Y2', 'r'], { match: ['q', 'w', 'Y2'], relay: ['Y2', 'r'] }],
  ['E', ['Y2', 'r'], ['E_done'], { match: ['Y2', 'r'] }],
];

/**
 * S union N ⊕ M (research nets `tjnUnion`): `a` mints onto `p`; the join `b` on (`p`, `s`)
 * relays to the carrier `q`; `c` relays `q` into `s` and `r`; `d` drains `r`. `s` is filled only
 * by `c`, after `b`, so `b` is dead. Budget SUPPLY, carrier q. Derived label: deadlock after `a`.
 */
export const UNION_ROWS: readonly Row[] = [
  ['a', ['SUPPLY'], ['p']],
  ['b', ['p', 's'], ['q'], { match: ['p', 's'], relay: ['q'] }],
  ['c', ['q'], ['s', 'r']],
  ['d', ['r'], ['d_done']],
];

/**
 * NU-054 AC3 join chain: the mint `fork` co-mints one name onto `A`, `B`, `D`; `j1` joins `A`,
 * `B` and relays to `C`; `j2` joins `C`, `D` onto `done`.
 */
export const JOIN_CHAIN_ROWS: readonly Row[] = [
  ['fork', ['S'], ['A', 'B', 'D']],
  ['j1', ['A', 'B'], ['C'], { match: ['A', 'B'], relay: ['C'] }],
  ['j2', ['C', 'D'], ['done'], { match: ['C', 'D'] }],
];

/** AC3's variant: `D` comes from a second, independent mint, so `j2` can never match. */
export const JOIN_CHAIN_SPLIT_ROWS: readonly Row[] = [
  ['fork', ['S'], ['A', 'B']],
  ['mint2', ['S2'], ['D']],
  ['j1', ['A', 'B'], ['C'], { match: ['A', 'B'], relay: ['C'] }],
  ['j2', ['C', 'D'], ['done'], { match: ['C', 'D'] }],
];
