/**
 * @module counterexample-decoder
 *
 * Decodes z3's refutation output into replayable counterexample material.
 *
 * There is exactly one decoder: {@link decodeStateSet}, which collects the ground
 * `Reachable` facts of a `:produce-proofs` refutation into a SET. The ordered trace
 * a caller sees is reconstructed from that set by the abstract replayer; the proof
 * printer's traversal order is not a firing order and was never safe to read as one.
 *
 * Applications with non-ground arguments (rule bodies quantify `Reachable` over
 * variables) or the wrong arity are skipped; a malformed proof simply yields a
 * smaller (possibly empty) set, never a throw. Byte-for-byte mirror of the Rust
 * `counterexample::decode_state_set`.
 */
import { MarkingState } from '../marking-state.js';
import type { FlatNet } from '../encoding/flat-net.js';
import { sexprEnd } from './smt-text.js';

/** Result of counterexample decoding. */
export interface DecodedTrace {
  /**
   * The ground `Reachable` markings of the proof as an order-free set (text order
   * preserved for display), what the abstract replayer chains into a firing order.
   */
  readonly states: ReadonlySet<MarkingState>;
  /** Why nothing was decoded; `null` when `states` is non-empty. */
  readonly note: string | null;
}

/** Decodes the states of a z3 reply; a note says so when none were found. */
export function decode(answer: string, flatNet: FlatNet): DecodedTrace {
  const states = decodeStateSet(answer, flatNet);
  return { states, note: states.size === 0 ? 'no ground Reachable states in the z3 proof' : null };
}

/**
 * Collects the ground `Reachable(...)` applications from a z3 refutation proof into
 * a state set, in text order.
 */
export function decodeStateSet(answer: string, flatNet: FlatNet): ReadonlySet<MarkingState> {
  const byKey = new Map<string, MarkingState>();
  const P = flatNet.places.length;
  for (const head of ['(Reachable', '(|Reachable|']) {
    let from = 0;
    for (;;) {
      const start = answer.indexOf(head, from);
      if (start < 0) break;
      from = start + head.length;
      // Word boundary: "(Reachable" must not match "(ReachableFoo …".
      if (head === '(Reachable') {
        const next = answer[from];
        if (next == null || !(/\s/.test(next) || next === ')')) continue;
      }
      const end = sexprEnd(answer, start);
      if (end < 0) break;
      const inner = answer.slice(start + head.length, end - 1);
      const args = parseGroundIntArgs(inner);
      if (args != null && args.length === P) {
        const marking = toMarking(args, flatNet);
        const key = marking.toString();
        if (!byKey.has(key)) byKey.set(key, marking);
      }
    }
  }
  return new Set(byKey.values());
}

function toMarking(args: readonly number[], flatNet: FlatNet): MarkingState {
  const builder = MarkingState.builder();
  for (let i = 0; i < args.length; i++) {
    if (args[i]! > 0) builder.tokens(flatNet.places[i]!, args[i]!);
  }
  return builder.build();
}

/**
 * Parses an application's argument text into integers, accepting only GROUND
 * arguments: bare integer literals (`3`, `-1`) and the SMT-LIB negation form
 * `(- 3)`. Any other token (a bound variable, a nested expression) makes the
 * application non-ground: returns `null`.
 */
export function parseGroundIntArgs(inner: string): number[] | null {
  const args: number[] = [];
  let rest = inner.trimStart();
  while (rest !== '') {
    if (rest.startsWith('(')) {
      const stripped = rest.slice(1);
      const close = stripped.indexOf(')');
      if (close < 0) return null;
      const body = stripped.slice(0, close);
      if (body.includes('(')) return null;
      const trimmed = body.trim();
      if (!trimmed.startsWith('-')) return null;
      const n = parseInt64(trimmed.slice(1).trim());
      if (n == null) return null;
      args.push(-n);
      rest = stripped.slice(close + 1).trimStart();
    } else {
      let tokenEnd = rest.length;
      for (let i = 0; i < rest.length; i++) {
        const c = rest[i]!;
        if (/\s/.test(c) || c === '(' || c === ')') {
          tokenEnd = i;
          break;
        }
      }
      const n = parseInt64(rest.slice(0, tokenEnd));
      if (n == null) return null;
      args.push(n);
      rest = rest.slice(tokenEnd).trimStart();
    }
  }
  return args;
}

function parseInt64(token: string): number | null {
  return /^-?\d+$/.test(token) ? Number(token) : null;
}
