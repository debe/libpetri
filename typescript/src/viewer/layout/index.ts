/**
 * Public re-exports of the C0 layout pipeline.
 *
 * Exists so external Node tooling (e.g. the prerender CLI in
 * `scripts/prerender-c0.mjs`) and the Java javadoc taglet's hybrid path
 * can consume the pipeline through a stable specifier — `libpetri/viewer/layout`
 * once published, or `dist/viewer/layout/index.js` from the repo.
 *
 * The viewer's own `mount()` calls these functions through `render.ts` and
 * does not import this barrel.
 *
 * @module viewer/layout
 */

export {
  parseLibpetriDot,
  foldOrphans,
  replicateShared,
  type ArcType,
  type NodeKind,
  type ParsedNode,
  type ParsedEdge,
  type ParsedCluster,
  type GraphModel,
  type ReplicateOptions,
  type ReplicateStats,
} from './preprocess.js';

export {
  elkLayout,
  writeBack,
  type NodePosition,
  type ClusterBox,
  type LayoutResult,
} from './elk-place.js';
