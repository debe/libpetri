/**
 * DOT → SVG rendering for the canonical libpetri viewer.
 *
 * Wraps `@viz-js/viz` and memoizes the wasm-backed instance so multiple
 * `mount()` calls on the same page reuse a single Viz instance. Behaviour
 * matches the older `render-dom` module byte-for-byte; see {@link render-dom}
 * for the original. This file exists so the viewer module is self-contained
 * and can be bundled as an IIFE for embedding into the doclet/Javadoc/Rustdoc
 * outputs.
 *
 * Browser-only: requires `@viz-js/viz` at runtime.
 *
 * @module viewer/render
 */

import { instance as vizInstance } from '@viz-js/viz';

type Viz = Awaited<ReturnType<typeof vizInstance>>;

let vizPromise: Promise<Viz> | null = null;

/** Memoize the viz.js instance so the wasm loads only once per page. */
export function getViz(): Promise<Viz> {
  if (!vizPromise) vizPromise = vizInstance();
  return vizPromise;
}

/**
 * Render a DOT source string to an SVGSVGElement.
 *
 * Layout engine is pinned to `dot` (deterministic across runs); libpetri
 * exporters emit byte-stable DOT per spec EXP-014 so the same DOT yields
 * the same SVG.
 */
export async function renderDotToSvg(dotSource: string): Promise<SVGSVGElement> {
  const viz = await getViz();
  return viz.renderSVGElement(dotSource, { engine: 'dot' });
}
