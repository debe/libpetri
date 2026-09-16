/**
 * @module parikh-search
 *
 * The witness search of the state-equation phase (VER-018): a breadth-first search
 * from `M0` under the exact abstract semantics ({@link enabledA} / {@link fireA} —
 * consume-all and reset clearing, inhibitor and read guards) that fires each flat
 * transition at most as often as a candidate's firing counts allow, and stops at the
 * first marking that violates the property. This is the cheap first level of
 * directed reachability (Blondin, Haase and Offtermatt, TACAS 2021): the counts bound
 * the depth by their sum, which on a workflow net is small.
 *
 * `found` is a real firing sequence of the untimed net, so the violation it witnesses
 * is confirmed by construction. `none` is a completed search: no run whose firing
 * counts stay within the candidate's reaches a violation. `exhausted` means the node
 * budget stopped it and says nothing either way.
 *
 * Environment injection splits those three, because an injection is not a counted firing
 * and so is never searched. `found` survives it: the search fires only counted
 * transitions, a run in which the environment injects nothing is still a run of the net,
 * and the quiescence half of `Bad(M)` is judged with relax-env enablement — a marking it
 * accepts is stuck even against an environment free to inject. `none` does not survive
 * it: its claim is that no run reaches a violation, and an injected token could enable a
 * run the search never considered. So under injection the completed search reports
 * `exhausted`, which says nothing either way, rather than a negative it cannot support.
 */
import type { FlatNet } from '../encoding/flat-net.js';
import { enabledA, fireA, type AbstractState } from './abstract-replayer.js';

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
 * Searches the runs from `initial` that fire each transition `t` at most `counts[t]`
 * times for one that reaches a marking `isBad` accepts. A node is a marking together
 * with the counts still unspent, so two runs meeting there have the same future and
 * the second is dropped.
 *
 * Environment injection is not searched, so on a net with injected places a completed
 * search reports `exhausted` rather than `none`. A `found` run is still real — see the
 * module note.
 */
export function searchWithinCounts(
  flatNet: FlatNet,
  initial: AbstractState,
  counts: readonly number[],
  isBad: (state: AbstractState) => boolean,
  nodeBudget = 100_000,
): WitnessOutcome {
  const caps: [number, number][] = [];
  for (const [name, cap] of flatNet.environmentBounds) {
    const idx = flatNet.placeIndex.get(name);
    if (idx != null) caps.push([idx, cap]);
  }
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
  // The search ran out of counted runs, not out of budget. That settles `none` only when
  // nothing outside the counted firings can extend a run, so injection downgrades it.
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
