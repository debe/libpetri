/**
 * DOM rendering helper for libpetri DOT diagrams.
 *
 * Single source of truth for the viz.js + panzoom pipeline used by both
 * debug-ui (live sessions) and the internal dev-preview Vite app
 * (sample.dot iteration loop). Doc generators (Javadoc taglet, Rustdoc
 * build.rs, TypeDoc plugin) take a different path — they shell out to the
 * Graphviz `dot` binary at build time — and do not consume this module.
 *
 * Browser-only: requires `@viz-js/viz` and `panzoom` as peer dependencies.
 *
 * @module render-dom
 */

import { instance as vizInstance } from '@viz-js/viz';
import panzoom from 'panzoom';

type Viz = Awaited<ReturnType<typeof vizInstance>>;
export type PanzoomInstance = ReturnType<typeof panzoom>;

let vizPromise: Promise<Viz> | null = null;

/** Memoizes the viz.js instance so loading happens only once per page. */
function getViz(): Promise<Viz> {
  if (!vizPromise) vizPromise = vizInstance();
  return vizPromise;
}

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
  readonly panzoom?: Parameters<typeof panzoom>[1];
}

export interface RenderDotResult {
  readonly svg: SVGSVGElement;
  readonly panzoom: PanzoomInstance;
}

/**
 * Default panzoom configuration shared by debug-ui and the dev preview.
 *
 * - `maxZoom: 1000` — effectively unlimited; lets users dive into ~150-node
 *   diagrams without hitting an artificial ceiling.
 * - `minZoom: 0.02` — allows fitting very large nets in a small viewport.
 * - `smoothScroll: false` — sharper interactive feel.
 * - `zoomDoubleClickSpeed: 1` — single-click double-zoom toggle.
 */
export const DEFAULT_PANZOOM_OPTS = {
  smoothScroll: false,
  zoomDoubleClickSpeed: 1,
  maxZoom: 1000,
  minZoom: 0.02,
} as const satisfies Parameters<typeof panzoom>[1];

/**
 * Render a DOT string into a container element and wrap it with panzoom.
 *
 * Engine is pinned to `'dot'` so layout is deterministic across reloads;
 * libpetri mappers emit byte-stable DOT (per spec EXP-014) and the `dot`
 * engine produces identical SVG for identical input.
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
  const viz = await getViz();
  const svg = viz.renderSVGElement(dotSource, { engine: 'dot' });

  container.innerHTML = '';
  container.appendChild(svg);

  if (opts.previousPanzoom) {
    opts.previousPanzoom.dispose();
  }

  const panzoomOpts = { ...DEFAULT_PANZOOM_OPTS, ...opts.panzoom };
  const instance = panzoom(svg, panzoomOpts);

  return { svg, panzoom: instance };
}
