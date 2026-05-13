/**
 * Pan/zoom wrapper for the canonical libpetri viewer.
 *
 * Delegates to the `panzoom` library (no hand-rolled wheel handlers — we
 * intentionally drop the IIFE/javadoc version's bespoke math in favour of
 * a single battle-tested implementation). Defaults match the old debug-ui
 * and dev-preview values so the canonical viewer feels identical to what
 * users had before.
 *
 * @module viewer/pan-zoom
 */

import panzoom from 'panzoom';

export type PanzoomInstance = ReturnType<typeof panzoom>;
export type PanzoomOptions = Parameters<typeof panzoom>[1];

/**
 * Default panzoom configuration shared across all viewer surfaces.
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
} as const satisfies PanzoomOptions;

/**
 * Attach panzoom to a freshly rendered SVG element. The caller is
 * responsible for disposing any previous instance (or pass it as
 * `previous` to dispose it here).
 */
export function attachPanzoom(
  svg: SVGSVGElement,
  options?: PanzoomOptions,
  previous?: PanzoomInstance | null,
): PanzoomInstance {
  if (previous) {
    try {
      previous.dispose();
    } catch {
      // Swallow disposal errors — the previous instance may already be
      // detached or the panzoom internals may have raised on a missing
      // root node. Either way we just want a fresh instance.
    }
  }
  const opts = { ...DEFAULT_PANZOOM_OPTS, ...options };
  return panzoom(svg, opts);
}
