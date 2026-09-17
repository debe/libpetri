/**
 * @module parikh-search
 *
 * The witness search of the state-equation phase (VER-018): breadth-first from `M0` under
 * the exact abstract semantics ({@link enabledA} / {@link fireA}), firing each flat
 * transition at most as often as a candidate's counts allow, stopping at the first
 * violating marking. The counts bound the depth by their sum (Blondin, Haase and
 * Offtermatt, TACAS 2021).
 *
 * `found` is a real firing sequence, so its violation is confirmed. `none` means no run
 * within the counts reaches a violation. `exhausted` says nothing either way.
 *
 * Injection is not a counted firing and is never searched. `found` still stands: a run
 * without injection is a run of the net, and `Bad(M)` judges quiescence with relax-env
 * enablement. `none` does not, since an injected token could enable an unsearched run, so
 * under injection a completed search reports `exhausted`.
 */
import type { FlatNet } from '../encoding/flat-net.js';
import { enabledA, environmentCaps, fireA, type AbstractState } from './abstract-replayer.js';

/** Outcome of {@link searchWithinCounts}. */
export type WitnessOutcome =
  | {
      readonly kind: 'found';
      /** The markings of the run, `M0 … M_bad` inclusive. */
      readonly states: readonly AbstractState[];
      /** The flat transitions fired, one per consecutive pair of {@link states}. */
      readonly steps: readonly string[];
      readonly nodes: number;
    }
  | { readonly kind: 'none'; readonly nodes: number }
  | { readonly kind: 'exhausted'; readonly reason: string; readonly nodes: number };

interface SearchNode {
  readonly state: AbstractState;
  readonly remaining: readonly number[];
  readonly parent: number;
  readonly transition: number;
}

/**
 * Searches the runs from `initial` that fire each transition `t` at most `counts[t]` times
 * for one that reaches a marking `isBad` accepts. A node is a marking with its unspent
 * counts, so two runs meeting there share a future and the second is dropped.
 */
export function searchWithinCounts(
  flatNet: FlatNet,
  initial: AbstractState,
  counts: readonly number[],
  isBad: (state: AbstractState) => boolean,
  nodeBudget = 100_000,
): WitnessOutcome {
  const caps = environmentCaps(flatNet);
  const nodes: SearchNode[] = [{ state: initial, remaining: counts, parent: -1, transition: -1 }];
  if (isBad(initial)) return { kind: 'found', states: [initial], steps: [], nodes: 1 };
  const seen = new Set<string>([key(initial, counts)]);
  const transitions = flatNet.transitions;
  for (let head = 0; head < nodes.length; head++) {
    const node = nodes[head]!;
    for (let t = 0; t < transitions.length; t++) {
      if (node.remaining[t]! <= 0) continue;
      const ft = transitions[t]!;
      if (!enabledA(node.state, ft)) continue;
      const next = fireA(node.state, ft);
      if (caps.some(([idx, cap]) => next[idx]! > cap)) continue;
      const remaining = [...node.remaining];
      remaining[t]!--;
      const k = key(next, remaining);
      if (seen.has(k)) continue;
      if (nodes.length >= nodeBudget) {
        return { kind: 'exhausted', reason: `search budget exhausted (${nodeBudget} nodes)`, nodes: nodes.length };
      }
      seen.add(k);
      nodes.push({ state: next, remaining, parent: head, transition: t });
      if (isBad(next)) return { kind: 'found', ...reconstruct(nodes, nodes.length - 1, flatNet), nodes: nodes.length };
    }
  }
  // Out of counted runs, not budget: `none` only when injection cannot extend a run.
  return flatNet.environmentInjection.size > 0
    ? { kind: 'exhausted', reason: 'environment injection is not searched', nodes: nodes.length }
    : { kind: 'none', nodes: nodes.length };
}

function key(state: AbstractState, remaining: readonly number[]): string {
  return `${state.join(',')}|${remaining.join(',')}`;
}

function reconstruct(
  nodes: readonly SearchNode[],
  last: number,
  flatNet: FlatNet,
): { states: AbstractState[]; steps: string[] } {
  const states: AbstractState[] = [];
  const steps: string[] = [];
  for (let i = last; i >= 0; i = nodes[i]!.parent) {
    const node = nodes[i]!;
    states.push(node.state);
    if (node.transition >= 0) steps.push(flatNet.transitions[node.transition]!.name);
  }
  states.reverse();
  steps.reverse();
  return { states, steps };
}
