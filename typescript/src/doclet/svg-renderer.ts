/**
 * SVG renderer using `@viz-js/viz` (Graphviz WASM).
 *
 * Pure WASM — zero external dependencies. No system `dot` binary required.
 *
 * Mirrors: Java's `PetriNetTaglet.dotToSvg()` (which uses `dot -Tsvg` subprocess)
 *
 * @module doclet/svg-renderer
 */

/**
 * Renders a DOT string to SVG using the `@viz-js/viz` WASM engine.
 *
 * Strips the XML prolog/DOCTYPE and explicit width/height attributes so the SVG
 * scales via viewBox + CSS instead of overriding with fixed pt sizes.
 *
 * @param dot - the DOT source string
 * @returns SVG markup string
 * @throws if `@viz-js/viz` is not installed or DOT parsing fails
 */
export async function dotToSvg(dot: string): Promise<string> {
  // Dynamic import — @viz-js/viz is an optional peer dependency
  const { instance } = await import('@viz-js/viz');
  const viz = await instance();
  let svg = viz.renderString(dot, { format: 'svg', engine: 'dot' });

  // Strip XML prolog and DOCTYPE — invalid inside HTML5
  const svgStart = svg.indexOf('<svg');
  if (svgStart > 0) svg = svg.substring(svgStart);

  // Strip explicit width/height attributes (e.g. "1942pt") so the SVG
  // scales via viewBox + CSS instead of overriding with fixed pt sizes
  svg = svg.replace(/\s+(?:width|height)="[^"]*"/g, '');

  return svg;
}
