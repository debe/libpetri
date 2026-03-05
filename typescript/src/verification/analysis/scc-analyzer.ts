/**
 * Strongly Connected Component analysis using Tarjan's algorithm.
 * Generic over node type T. Uses a key function for Map-based lookups.
 */

/** Computes all SCCs in a graph. O(V + E) via Tarjan's algorithm. */
export function computeSCCs<T>(
  nodes: Iterable<T>,
  successors: (node: T) => Iterable<T>,
): Set<T>[] {
  const nodeArray = [...nodes];
  const indexMap = new Map<T, number>();
  const lowlink = new Map<T, number>();
  const onStack = new Set<T>();
  const stack: T[] = [];
  const sccs: Set<T>[] = [];
  let index = 0;

  function strongConnect(v: T): void {
    indexMap.set(v, index);
    lowlink.set(v, index);
    index++;
    stack.push(v);
    onStack.add(v);

    for (const w of successors(v)) {
      if (!indexMap.has(w)) {
        strongConnect(w);
        lowlink.set(v, Math.min(lowlink.get(v)!, lowlink.get(w)!));
      } else if (onStack.has(w)) {
        lowlink.set(v, Math.min(lowlink.get(v)!, indexMap.get(w)!));
      }
    }

    if (lowlink.get(v) === indexMap.get(v)) {
      const scc = new Set<T>();
      let w: T;
      do {
        w = stack.pop()!;
        onStack.delete(w);
        scc.add(w);
      } while (w !== v);
      sccs.push(scc);
    }
  }

  for (const node of nodeArray) {
    if (!indexMap.has(node)) {
      strongConnect(node);
    }
  }

  return sccs;
}

/** Finds terminal (bottom) SCCs — SCCs with no outgoing edges to other SCCs. */
export function findTerminalSCCs<T>(
  nodes: Iterable<T>,
  successors: (node: T) => Iterable<T>,
): Set<T>[] {
  const allSCCs = computeSCCs(nodes, successors);

  const terminal: Set<T>[] = [];
  for (const scc of allSCCs) {
    let isTerminal = true;
    for (const node of scc) {
      for (const succ of successors(node)) {
        if (!scc.has(succ)) {
          isTerminal = false;
          break;
        }
      }
      if (!isTerminal) break;
    }
    if (isTerminal) {
      terminal.push(scc);
    }
  }

  return terminal;
}
