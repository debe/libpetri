/**
 * DOT → SVG rendering for the canonical libpetri viewer.
 *
 * Two render paths:
 *
 *   renderDotToSvg(dot)                — plain Graphviz `dot` engine.
 *   renderDotToSvgWithElkLayout(dot)   — C0 pipeline: parse → fold →
 *                                        replicate → ELK → writeBack →
 *                                        Graphviz `nop2` (pinned nodes AND
 *                                        edge routes). Cached by DOT hash.
 *
 * The ELK path is the default for {@link mount}; the plain-Graphviz path
 * remains as a fallback for callers that want stock layout (or for
 * environments where elkjs isn't installed).
 *
 * The ELK stage is pulled in by dynamic import rather than at module load, so
 * the plain-Graphviz path genuinely works without `elkjs` present. Under a
 * static import the whole module failed to load and `layout: 'graphviz'` was
 * an escape hatch that could never be reached.
 *
 * @module viewer/render
 */

import { instance as vizInstance } from '@viz-js/viz';
import type { ElkLayoutConfig } from './layout/elk-place.js';

type Viz = Awaited<ReturnType<typeof vizInstance>>;

let vizPromise: Promise<Viz> | null = null;

/** Memoize the viz.js instance so the wasm loads only once per page. */
export function getViz(): Promise<Viz> {
  if (!vizPromise) vizPromise = vizInstance();
  return vizPromise;
}

/**
 * Render a DOT source string to an SVGSVGElement using the plain `dot`
 * engine. Deterministic across runs; libpetri exporters emit byte-stable
 * DOT per spec EXP-014 so the same DOT yields the same SVG.
 */
export async function renderDotToSvg(dotSource: string): Promise<SVGSVGElement> {
  const viz = await getViz();
  return viz.renderSVGElement(dotSource, { engine: 'dot' });
}

// ---- C0 / ELK pin-mode cache ---------------------------------------------

/** FNV-1a 32-bit hash. Fast enough that a SHA isn't worth the import. */
function fnv1a(input: string): string {
  let h = 0x811c9dc5;
  for (let i = 0; i < input.length; i++) {
    h ^= input.charCodeAt(i);
    h = Math.imul(h, 0x01000193);
  }
  return (h >>> 0).toString(16);
}

const PINNED_DOT_CACHE_CAP = 16;
const pinnedDotCache = new Map<string, string>();

function getCachedPinnedDot(key: string): string | undefined {
  const hit = pinnedDotCache.get(key);
  if (hit !== undefined) {
    // LRU touch: re-insert moves to most-recent position in Map ordering.
    pinnedDotCache.delete(key);
    pinnedDotCache.set(key, hit);
  }
  return hit;
}

function setCachedPinnedDot(key: string, value: string): void {
  pinnedDotCache.set(key, value);
  while (pinnedDotCache.size > PINNED_DOT_CACHE_CAP) {
    const oldest = pinnedDotCache.keys().next().value;
    if (oldest === undefined) break;
    pinnedDotCache.delete(oldest);
  }
}

/** Test helper — clears the pinned-DOT LRU cache between mounts. */
export function _clearElkLayoutCache(): void {
  pinnedDotCache.clear();
}

/**
 * Run the C0 layout pipeline against a libpetri DOT source and return the
 * rendered SVG. The expensive steps (preprocess + ELK layout + DOT rewrite)
 * are cached keyed on the input DOT's hash plus the layout config, so
 * re-mounts on the same net structure and config skip everything except the
 * Graphviz pin-mode draw.
 *
 * Per-tick marking updates do NOT call this — they toggle classes on the
 * already-mounted SVG. ELK only runs when the net structure changes.
 *
 * `cfg` tunes the ELK stage — see {@link ElkLayoutConfig}.
 */
export async function renderDotToSvgWithElkLayout(
  dotSource: string,
  cfg?: ElkLayoutConfig,
): Promise<SVGSVGElement> {
  const key = fnv1a(dotSource + '\0' + JSON.stringify(cfg ?? {}));
  let pinnedDot = getCachedPinnedDot(key);
  if (pinnedDot === undefined) {
    const { foldOrphans, parseLibpetriDot, replicateShared } =
      await import('./layout/preprocess.js');
    // `elkjs` is an optional peer dependency, in line with the viewer's other
    // browser-only peers. Name it explicitly here: the raw resolution failure
    // mentions a deep path inside elkjs and reads as a libpetri bug.
    const { elkLayout, writeBack } = await import('./layout/elk-place.js').catch(
      (cause: unknown) => {
        throw new Error(
          "the viewer's default 'elk' layout requires the optional peer "
            + "dependency 'elkjs'. Install it, or pass { layout: 'graphviz' } "
            + 'to mount() for stock Graphviz layout with spline edges.',
          { cause },
        );
      },
    );
    const graph = replicateShared(
      foldOrphans(parseLibpetriDot(dotSource), 0.7),
      { max: Infinity },
    );
    const layout = await elkLayout(graph, cfg);
    pinnedDot = writeBack(graph, layout);
    setCachedPinnedDot(key, pinnedDot);
  }
  const viz = await getViz();
  return viz.renderSVGElement(pinnedDot, {
    // nop2 draws the pinned node positions AND our ELK-computed orthogonal
    // edge routes verbatim. See writeBack/edgePosSpline: we route edges
    // ourselves rather than let Graphviz's ortho router run, which crashes
    // the wasm on large nets.
    engine: 'nop2',
    yInvert: true,
  });
}
