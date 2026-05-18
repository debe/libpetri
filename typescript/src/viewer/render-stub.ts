/**
 * Static-bundle replacement for `./render.ts`.
 *
 * The IIFE build for `viewer-static.iife.js` aliases `./render.js` to this
 * module via an esbuild `onResolve` plugin, so the slim bundle does not
 * import `@viz-js/viz` and ships no Graphviz WASM payload.
 *
 * Both exports throw if called — the static bundle's `mount()` is intended
 * to adopt an SVG that's already present in the host. Reaching this stub
 * means a caller passed DOT into the static bundle, which is a usage bug.
 *
 * @module viewer/render-stub
 */

export async function renderDotToSvg(_dotSource: string): Promise<SVGSVGElement> {
  throw new Error(
    'libpetri viewer: static bundle has no DOT renderer. Either ship the ' +
      'pre-rendered SVG in the host (mount(null, container, opts)) or load ' +
      'the full viewer.iife.js bundle.',
  );
}

export function getViz(): never {
  throw new Error('libpetri viewer: static bundle has no Viz instance.');
}
