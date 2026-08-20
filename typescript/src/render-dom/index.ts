/**
 * Compatibility wrapper over the canonical viewer.
 *
 * This module predates `libpetri/viewer` and used to be the shared viz.js +
 * panzoom pipeline behind debug-ui and the dev-preview app. Both moved to the
 * canonical viewer at `274cb41`, and the doc generators (Javadoc taglet,
 * `libpetri-docgen`, TypeDoc plugin) never shelled out to a `dot` binary
 * again either: they embed the viewer IIFE and mount client-side.
 *
 * What was left behind was a public export that still pinned Graphviz
 * `engine: 'dot'`, so anything reaching for it got stock spline layout with
 * diagonal edges while every first-party surface rendered ELK-placed nodes
 * with orthogonal routes. `renderDotToContainer` now delegates to
 * {@link mount}, so all render paths agree.
 *
 * Prefer importing `libpetri/viewer` directly in new code: `mount()` returns a
 * {@link ViewerHandle} with cluster collapse, subnet toggling, filtering and
 * highlight control, of which this wrapper surfaces only the SVG and the
 * panzoom instance.
 *
 * Browser-only. Requires `@viz-js/viz`, `panzoom`, and `elkjs` (the viewer's
 * default layout) as peer dependencies.
 *
 * @module render-dom
 */

import {
  DEFAULT_PANZOOM_OPTS,
  mount,
  type PanzoomInstance,
  type PanzoomOptions,
  type ViewerHandle,
} from '../viewer/index.js';

export type { PanzoomInstance, PanzoomOptions };

/**
 * Default panzoom configuration.
 *
 * Re-exported from the viewer rather than redefined here; a second copy of
 * these numbers is exactly how the two render paths drifted apart in the first
 * place.
 */
export { DEFAULT_PANZOOM_OPTS };

export interface RenderDotOptions {
  /**
   * Existing panzoom instance to dispose before initializing a new one.
   * Pass the value previously returned from {@link renderDotToContainer}
   * so callers don't need to track it themselves.
   */
  readonly previousPanzoom?: PanzoomInstance | null;
  /**
   * Per-call panzoom overrides. Merged on top of {@link DEFAULT_PANZOOM_OPTS},
   * so partial overrides keep the unspecified defaults (e.g. passing only
   * `smoothScroll: true` retains `maxZoom: 1000` and `minZoom: 0.02`).
   */
  readonly panzoom?: PanzoomOptions;
}

export interface RenderDotResult {
  readonly svg: SVGSVGElement;
  readonly panzoom: PanzoomInstance;
}

/**
 * Render a DOT string into a container element and wrap it with panzoom.
 *
 * Layout is the viewer default: ELK node placement plus ELK-computed
 * orthogonal edge routes, drawn by Graphviz `nop2`. Deterministic across
 * reloads, since libpetri mappers emit byte-stable DOT (spec EXP-014) and
 * neither stage introduces randomness.
 *
 * The container's existing children are removed before the new SVG is
 * appended.
 *
 * @returns the rendered SVG element and the panzoom instance, so callers
 * can build secondary indexes (node caches, highlighting state) on the SVG
 * and dispose the panzoom on the next render.
 */
export async function renderDotToContainer(
  dotSource: string,
  container: HTMLElement,
  opts: RenderDotOptions = {},
): Promise<RenderDotResult> {
  // Disposed up front rather than after the swap (the pre-viewer ordering):
  // the old instance is bound to nodes `mount` is about to discard, and a
  // panzoom still listening on a detached subtree has nothing useful to do.
  if (opts.previousPanzoom) {
    try {
      opts.previousPanzoom.dispose();
    } catch {
      // Already detached, or panzoom raised on a missing root. Either way the
      // only goal was to stop the old instance.
    }
  }

  const handle: ViewerHandle = await mount(dotSource, container, {
    chrome: false,
    panzoom: opts.panzoom,
  });

  return { svg: handle.svg, panzoom: handle.panzoom };
}
