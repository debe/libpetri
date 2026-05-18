/**
 * Static entrypoint for the libpetri viewer — re-exports the public API of
 * `./index.js` but is bundled (in the IIFE build) with `./render.js` aliased
 * to a throwing stub. The resulting IIFE has no DOT renderer and no
 * `@viz-js/viz` payload, and is intended for hosts that already embed a
 * pre-rendered `<svg>` (e.g. Java javadoc taglet emitting `dot -Tsvg` at
 * build time).
 *
 * Callers MUST invoke `mount(null, container, opts)` — passing a DOT string
 * through the static bundle throws.
 *
 * @module viewer/index-static
 */

export { mount } from './index.js';
export {
  colorForPrefix,
  discoverClusters,
  VIEWER_CSS_VARIABLES,
  DEFAULT_PANZOOM_OPTS,
} from './index.js';
export type {
  ClusterDescriptor,
  ViewerHandle,
  MountOptions,
  PanzoomInstance,
  PanzoomOptions,
} from './index.js';
