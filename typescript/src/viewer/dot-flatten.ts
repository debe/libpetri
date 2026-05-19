/**
 * Strip `subgraph cluster_*` wrappers from a libpetri-generated DOT source,
 * producing an equivalent flat graph (no visual grouping). The returned
 * DOT contains every node and edge from the input — only the cluster
 * scope markers and their cluster-level attribute statements are dropped.
 *
 * Cross-cluster invisible edges that carry `ltail`/`lhead` attributes
 * targeting `cluster_*` have those attributes removed (the references
 * become dangling once clusters are gone; Graphviz warns about them).
 * The edges themselves are kept so layout rank hints survive the flatten.
 *
 * The transform assumes libpetri's byte-stable DOT shape (spec EXP-014):
 *  - one statement per line, terminated by `;`
 *  - `subgraph cluster_<id> {` and matching `}` each on their own line
 *  - inside a cluster, cluster-level attributes are bare `key=value;`
 *    lines (no `[`), node declarations carry `[`, edges carry `->`
 *
 * The function is idempotent: passing already-flat DOT through returns
 * a string equal to the input (modulo whitespace introduced by re-joining).
 *
 * @module viewer/dot-flatten
 */

const CLUSTER_OPEN = /^\s*subgraph\s+cluster_[A-Za-z0-9_]+\s*\{\s*$/;
const ONLY_CLOSE_BRACE = /^\s*\}\s*$/;

/**
 * Strip cluster wrappers from a libpetri DOT source. Returns flat DOT
 * that renders the same nodes and edges without subgraph groupings.
 */
export function flattenClusters(dot: string): string {
  const lines = dot.split('\n');
  const out: string[] = [];
  let clusterDepth = 0;

  for (const line of lines) {
    if (CLUSTER_OPEN.test(line)) {
      clusterDepth++;
      continue;
    }
    if (clusterDepth > 0) {
      if (ONLY_CLOSE_BRACE.test(line)) {
        clusterDepth--;
        continue;
      }
      // Inside a cluster: keep node decls (have `[`) and edges (have `->`).
      // Drop cluster-attribute statements (label=, style=, bgcolor=, ...).
      if (line.includes('[') || line.includes('->')) {
        out.push(stripClusterEdgeAttrs(line));
      }
      continue;
    }
    // Top level: cross-cluster edges live here; drop their cluster refs.
    if (line.includes('->') && (line.includes('ltail=') || line.includes('lhead='))) {
      out.push(stripClusterEdgeAttrs(line));
      continue;
    }
    out.push(line);
  }

  return out.join('\n');
}

function stripClusterEdgeAttrs(line: string): string {
  // Handle each `ltail`/`lhead` whether it's the first attribute in the
  // bracket group or a later one. Quoted cluster names only — libpetri
  // emits them as `ltail="cluster_xxx"`.
  return line
    .replace(/,\s*ltail="cluster_[^"]*"/g, '')
    .replace(/,\s*lhead="cluster_[^"]*"/g, '')
    .replace(/\[\s*ltail="cluster_[^"]*"\s*,\s*/g, '[')
    .replace(/\[\s*lhead="cluster_[^"]*"\s*,\s*/g, '[')
    .replace(/\[\s*ltail="cluster_[^"]*"\s*\]/g, '[]')
    .replace(/\[\s*lhead="cluster_[^"]*"\s*\]/g, '[]');
}
