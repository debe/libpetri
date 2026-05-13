/**
 * Canonical libpetri Petri-net diagram viewer.
 *
 * Single source of truth for DOT → SVG rendering + cluster overlay across
 * all four surfaces:
 *  - debug-ui (live debugger)
 *  - dev-preview (Vite app)
 *  - Javadoc taglet (Java doclet)
 *  - Rustdoc embed (libpetri-docgen)
 *  - TypeDoc / typescript doclet
 *
 * Build outputs:
 *  - ESM: `dist/viewer/index.js` — consumed by Vite/Webpack/Node bundlers.
 *  - IIFE: `dist/viewer/viewer.iife.js` — self-contained, exposes
 *    `window.LibpetriViewer = { mount, ... }`. Used by the doc taglets
 *    that ship pre-rendered HTML pages without a bundler.
 *  - CSS: `dist/viewer/viewer.css` — canonical stylesheet (copied from
 *    `src/viewer/resources/viewer.css`).
 *
 * Edits to viewer behaviour MUST happen here. The three resource directories
 * under `java/`, `rust/`, and `typescript/src/doclet/` are **build outputs**
 * populated by `scripts/build-viewer.sh` and must not be hand-edited.
 *
 * @module viewer
 */

import { renderDotToSvg } from './render.js';
import {
  attachPanzoom,
  DEFAULT_PANZOOM_OPTS,
  type PanzoomInstance,
  type PanzoomOptions,
} from './pan-zoom.js';
import {
  applyFilter as overlayApplyFilter,
  colorForPrefix,
  discoverClusters,
  isInsideCollapsedCluster as overlayIsInsideCollapsedCluster,
  paintClusterBorders,
  setClusterCollapsed,
  type ClusterDescriptor,
} from './cluster-overlay.js';
import { VIEWER_CSS_VARIABLES } from './styles.js';

export {
  colorForPrefix,
  discoverClusters,
  VIEWER_CSS_VARIABLES,
  DEFAULT_PANZOOM_OPTS,
};
export type { ClusterDescriptor, PanzoomInstance, PanzoomOptions };

/** Handle returned by {@link mount}. */
export interface ViewerHandle {
  /** The rendered root `<svg>` element. */
  readonly svg: SVGSVGElement;
  /** The panzoom instance attached to the SVG. */
  readonly panzoom: PanzoomInstance;
  /** Map of cluster prefix → descriptor for the current SVG. */
  readonly clusters: ReadonlyMap<string, ClusterDescriptor>;
  /** Prefixes currently marked collapsed on this handle. */
  readonly collapsedPrefixes: ReadonlySet<string>;
  /** Currently active "show only <prefix>" filter, or null. */
  readonly activeFilter: string | null;
  /** Collapse a single cluster by prefix. No-op if unknown. */
  collapse(prefix: string): void;
  /** Expand a single cluster by prefix. No-op if unknown. */
  expand(prefix: string): void;
  /** Collapse every discovered cluster. */
  collapseAll(): void;
  /** Expand every collapsed cluster. */
  expandAll(): void;
  /** Apply the "show only <prefix>" filter; pass `null` to clear. */
  filter(prefix: string | null): void;
  /** Reset pan/zoom to the identity transform. */
  resetZoom(): void;
  /** Reports whether `graphId` is inside a currently-collapsed cluster. */
  isInsideCollapsedCluster(graphId: string): boolean;
  /** Tear down: dispose panzoom and detach listeners. */
  dispose(): void;
}

/** Options accepted by {@link mount}. */
export interface MountOptions {
  /**
   * Previous handle to dispose before mounting. Pass the handle returned
   * by a prior `mount()` call so callers don't need to track it separately.
   * Cluster collapse / filter state from `previousHandle` is preserved
   * across the re-render so the user's intent survives a live re-draw.
   */
  readonly previousHandle?: ViewerHandle | null;
  /** Per-call panzoom overrides; merged on top of {@link DEFAULT_PANZOOM_OPTS}. */
  readonly panzoom?: PanzoomOptions;
  /** Fired after a cluster's collapsed state changes via the handle API. */
  readonly onClusterCollapse?: (prefix: string, collapsed: boolean) => void;
  /** Fired after `filter()` runs, with the new filter prefix or null. */
  readonly onClusterFilter?: (prefix: string | null) => void;
  /** When true, append a legend sidebar + filter chip strip inside `container`. */
  readonly chrome?: boolean;
}

/**
 * Render a DOT source, mount the resulting SVG into `container`, wire pan/zoom,
 * and surface cluster overlay controls.
 *
 * The container's existing children are removed before the new SVG is
 * appended (the same teardown behaviour `renderDotToContainer` used to provide).
 */
export async function mount(
  dotSource: string,
  container: HTMLElement,
  opts: MountOptions = {},
): Promise<ViewerHandle> {
  const previousHandle = opts.previousHandle ?? null;
  const preservedCollapsed = previousHandle
    ? new Set(previousHandle.collapsedPrefixes)
    : new Set<string>();
  const preservedFilter = previousHandle?.activeFilter ?? null;

  if (previousHandle) {
    previousHandle.dispose();
  }

  const svg = await renderDotToSvg(dotSource);

  container.innerHTML = '';
  container.appendChild(svg);
  // Tag the host so the canonical CSS (which scopes to .libpetri-viewer)
  // applies even when the consumer didn't wrap us in a .petrinet-diagram.
  container.classList.add('libpetri-viewer');

  const panzoomInstance = attachPanzoom(svg, opts.panzoom);
  const clusters = discoverClusters(svg);
  paintClusterBorders(clusters);

  const collapsedPrefixes = new Set<string>();
  let activeFilter: string | null = null;
  let disposed = false;

  // Chrome elements (created lazily; only when chrome:true is requested).
  // Re-rendering through the same handle does not duplicate them.
  let chromeRoot: HTMLElement | null = null;

  function ensureChrome(): void {
    if (!opts.chrome) return;
    if (chromeRoot && chromeRoot.parentNode === container) return;
    chromeRoot = document.createElement('div');
    chromeRoot.className = 'libpetri-viewer-chrome';
    chromeRoot.style.position = 'absolute';
    chromeRoot.style.inset = '0';
    chromeRoot.style.pointerEvents = 'none';

    const legend = document.createElement('div');
    legend.className = 'diagram-legend';
    legend.style.pointerEvents = 'auto';
    legend.innerHTML = '<div class="legend-title">Clusters</div>';
    chromeRoot.appendChild(legend);

    const strip = document.createElement('div');
    strip.className = 'diagram-filter-strip';
    strip.style.pointerEvents = 'auto';
    strip.innerHTML = '<span class="filter-strip-label">Show only:</span>';
    chromeRoot.appendChild(strip);

    // Position parent must be relative for the absolute chrome to anchor.
    if (getComputedStyle(container).position === 'static') {
      container.style.position = 'relative';
    }
    container.appendChild(chromeRoot);

    renderLegend(legend);
    renderFilterStrip(strip);
  }

  function renderLegend(legend: HTMLElement): void {
    legend.innerHTML = '<div class="legend-title">Clusters</div>';
    for (const cluster of clusters.values()) {
      const row = document.createElement('div');
      row.className = 'legend-row';
      row.innerHTML =
        '<span class="legend-ribbon" style="background:' + cluster.color + '"></span>' +
        '<span class="legend-label"></span>' +
        '<span class="legend-count"></span>';
      (row.querySelector('.legend-label') as HTMLElement).textContent = cluster.prefix;
      (row.querySelector('.legend-count') as HTMLElement).textContent = String(cluster.nodeCount);
      row.addEventListener('click', () => {
        if (collapsedPrefixes.has(cluster.prefix)) {
          handle.expand(cluster.prefix);
        } else {
          handle.collapse(cluster.prefix);
        }
      });
      legend.appendChild(row);
    }
  }

  function renderFilterStrip(strip: HTMLElement): void {
    strip.innerHTML = '<span class="filter-strip-label">Show only:</span>';
    const allChip = document.createElement('button');
    allChip.type = 'button';
    allChip.className = 'filter-chip filter-chip-all filter-chip-active';
    allChip.textContent = 'all';
    allChip.addEventListener('click', () => {
      handle.filter(null);
    });
    strip.appendChild(allChip);
    for (const cluster of clusters.values()) {
      const chip = document.createElement('button');
      chip.type = 'button';
      chip.className = 'filter-chip';
      chip.style.borderColor = cluster.color;
      chip.dataset.prefix = cluster.prefix;
      chip.innerHTML =
        '<span class="chip-dot" style="background:' + cluster.color + '"></span>';
      chip.append(document.createTextNode(cluster.prefix));
      chip.addEventListener('click', () => {
        if (activeFilter === cluster.prefix) {
          handle.filter(null);
        } else {
          handle.filter(cluster.prefix);
        }
      });
      strip.appendChild(chip);
    }
  }

  function refreshChromeActiveStates(): void {
    if (!chromeRoot) return;
    const strip = chromeRoot.querySelector('.diagram-filter-strip');
    if (!strip) return;
    strip.querySelectorAll<HTMLElement>('.filter-chip').forEach((chip) => {
      chip.classList.remove('filter-chip-active');
    });
    if (activeFilter === null) {
      strip
        .querySelector<HTMLElement>('.filter-chip-all')
        ?.classList.add('filter-chip-active');
    } else {
      strip
        .querySelector<HTMLElement>(`.filter-chip[data-prefix="${activeFilter}"]`)
        ?.classList.add('filter-chip-active');
    }
  }

  const handle: ViewerHandle = {
    svg,
    panzoom: panzoomInstance,
    clusters,
    get collapsedPrefixes() {
      return collapsedPrefixes;
    },
    get activeFilter() {
      return activeFilter;
    },
    collapse(prefix: string): void {
      if (disposed) return;
      const cluster = clusters.get(prefix);
      if (!cluster) return;
      if (!collapsedPrefixes.has(prefix)) {
        setClusterCollapsed(cluster, true);
        collapsedPrefixes.add(prefix);
        opts.onClusterCollapse?.(prefix, true);
      }
    },
    expand(prefix: string): void {
      if (disposed) return;
      const cluster = clusters.get(prefix);
      if (!cluster) return;
      if (collapsedPrefixes.has(prefix)) {
        setClusterCollapsed(cluster, false);
        collapsedPrefixes.delete(prefix);
        opts.onClusterCollapse?.(prefix, false);
      }
    },
    collapseAll(): void {
      if (disposed) return;
      for (const cluster of clusters.values()) {
        if (!collapsedPrefixes.has(cluster.prefix)) {
          setClusterCollapsed(cluster, true);
          collapsedPrefixes.add(cluster.prefix);
          opts.onClusterCollapse?.(cluster.prefix, true);
        }
      }
    },
    expandAll(): void {
      if (disposed) return;
      for (const prefix of Array.from(collapsedPrefixes)) {
        const cluster = clusters.get(prefix);
        if (!cluster) continue;
        setClusterCollapsed(cluster, false);
        collapsedPrefixes.delete(prefix);
        opts.onClusterCollapse?.(prefix, false);
      }
    },
    filter(prefix: string | null): void {
      if (disposed) return;
      activeFilter = prefix;
      overlayApplyFilter(svg, prefix);
      opts.onClusterFilter?.(prefix);
      refreshChromeActiveStates();
    },
    resetZoom(): void {
      if (disposed) return;
      try {
        panzoomInstance.moveTo(0, 0);
        panzoomInstance.zoomAbs(0, 0, 1);
      } catch {
        // panzoom internals can throw if the element was detached; ignore.
      }
    },
    isInsideCollapsedCluster(graphId: string): boolean {
      return overlayIsInsideCollapsedCluster(svg, clusters, collapsedPrefixes, graphId);
    },
    dispose(): void {
      if (disposed) return;
      disposed = true;
      try {
        panzoomInstance.dispose();
      } catch {
        // ignore
      }
      if (chromeRoot && chromeRoot.parentNode === container) {
        container.removeChild(chromeRoot);
      }
      chromeRoot = null;
    },
  };

  // Re-apply preserved collapse/filter state from the previous handle so
  // a live re-render (e.g. on marking-snapshot) keeps the user's selection.
  for (const prefix of preservedCollapsed) {
    handle.collapse(prefix);
  }
  if (preservedFilter !== null) {
    handle.filter(preservedFilter);
  }

  ensureChrome();

  return handle;
}
