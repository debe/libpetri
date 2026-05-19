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
import { annotateSvgForC0 } from './c0-annotations.js';
import { mountSidebar, type SidebarHandle } from './chrome/sidebar.js';
import { applyHighlight } from './highlight.js';
import { tagReplicas } from './replica-tagging.js';
import { applyVisibility, type VisibilityState } from './visibility.js';
import { VIEWER_CSS_VARIABLES } from './styles.js';
import { flattenClusters } from './dot-flatten.js';

export {
  colorForPrefix,
  discoverClusters,
  VIEWER_CSS_VARIABLES,
  DEFAULT_PANZOOM_OPTS,
};
export type { ClusterDescriptor, PanzoomInstance, PanzoomOptions };

/**
 * Subnet (cluster) visibility mode.
 *
 * - `'show'` — render the DOT as-is with `subgraph cluster_*` groupings
 *   visible (the default; the post-subnets layout).
 * - `'hide'` — render a flattened variant that drops cluster wrappers
 *   and the `ltail`/`lhead` cluster references on cross-cluster edges.
 *   Same nodes and edges, no visual grouping.
 */
export type SubnetVisibility = 'show' | 'hide';

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
  /** Current subnet visibility mode. */
  readonly subnets: SubnetVisibility;
  /**
   * Switch between the clustered (`'show'`) and flat (`'hide'`) views.
   * Triggers an internal re-mount via the canonical {@link mount} path —
   * the SVG is regenerated because Graphviz lays out cluster boundaries
   * during layout. Returns the new handle; the old one is disposed.
   *
   * After re-mount, the host container dispatches a bubbling
   * `libpetri-viewer:remount` CustomEvent whose `detail.handle` is the
   * fresh handle. Consumers that cache the handle (e.g. the debug-ui)
   * should listen on the container and update their reference.
   */
  setSubnets(mode: SubnetVisibility): Promise<ViewerHandle>;
  /** Flip {@link subnets} to the other mode and re-mount. See {@link setSubnets}. */
  toggleSubnets(): Promise<ViewerHandle>;
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
  /** Scale and translate so the full diagram fits the host viewport. */
  fit(): void;
  /** Reports whether `graphId` is inside a currently-collapsed cluster. */
  isInsideCollapsedCluster(graphId: string): boolean;
  /**
   * Highlight a node and every DOM copy of the same logical place; walk
   * junctions to surface real neighbors. Pass `null` to clear. C0-only.
   */
  highlight(nodeId: string | null): void;
  /** The node id currently highlighted, or `null`. */
  readonly highlightedNodeId: string | null;
  /**
   * Set the cluster-visibility state: which clusters render, and whether
   * directed-reachable orphans render. C0-only.
   */
  setVisibility(state: VisibilityState): void;
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
  /**
   * Layout strategy. `'elk'` (default) runs the C0 pipeline — parse → fold
   * → replicate → ELK → Graphviz `neato` pin mode — and tags replica
   * nodes for the click-all-copies + ⇄ overlay. `'graphviz'` runs the
   * plain Graphviz `dot` engine and skips replica tagging. The result is
   * cached on the DOT hash; re-mounts on identical DOT skip the pipeline.
   */
  readonly layout?: 'elk' | 'graphviz';
  /**
   * Initial subnet visibility mode. Defaults to `'show'` (clustered view).
   * Pass `'hide'` to mount with the flat view from the start. The chrome
   * button toggles between the two at runtime; see {@link ViewerHandle.setSubnets}.
   *
   * If `previousHandle` is supplied and `subnets` is omitted, the previous
   * handle's mode is inherited so live re-renders preserve the user's choice.
   */
  readonly subnets?: SubnetVisibility;
}

/**
 * Render a DOT source, mount the resulting SVG into `container`, wire pan/zoom,
 * and surface cluster overlay controls.
 *
 * The container's existing children are removed before the new SVG is
 * appended (the same teardown behaviour `renderDotToContainer` used to provide).
 *
 * Pass `dotSource === null` to adopt an SVG already present as a direct child
 * of `container` (pre-rendered SVG path — e.g. the Java javadoc taglet emits
 * `dot -Tsvg` at build time). In that mode the viewer never imports the
 * runtime DOT renderer, which lets the static IIFE bundle drop `@viz-js/viz`
 * entirely.
 *
 * NOTE: when shipping a pre-rendered SVG (`dotSource === null`), do NOT also
 * pass `previousHandle` — the handle's `dispose()` runs before SVG detection
 * and would orphan the host. The Java taglet mounts once per page so this is
 * a non-issue in practice.
 */
export async function mount(
  dotSource: string | null,
  container: HTMLElement,
  opts: MountOptions = {},
): Promise<ViewerHandle> {
  const previousHandle = opts.previousHandle ?? null;
  const preservedCollapsed = previousHandle
    ? new Set(previousHandle.collapsedPrefixes)
    : new Set<string>();
  const preservedFilter = previousHandle?.activeFilter ?? null;
  // Subnet mode: explicit opt wins, else inherit from previousHandle, else default to 'show'.
  const subnetsMode: SubnetVisibility =
    opts.subnets ?? previousHandle?.subnets ?? 'show';

  if (previousHandle) {
    previousHandle.dispose();
  }

  // Gate on dotSource (not on "SVG present") — debug-ui re-renders by
  // passing DOT with `previousHandle` and the leftover SVG must NOT be
  // misread as pre-rendered. Java passes literal `null` for the
  // pre-rendered path.
  let svg: SVGSVGElement;
  const existing = container.querySelector(':scope > svg');
  if (dotSource == null) {
    if (!(existing instanceof SVGSVGElement)) {
      throw new Error('mount: no DOT source and no pre-rendered SVG');
    }
    svg = existing;
  } else {
    // Dynamic import so the static IIFE entry can alias './render.js' to a
    // throwing stub and drop the @viz-js/viz + elkjs dependencies.
    const renderModule = await import('./render.js');
    const useElk = (opts.layout ?? 'elk') === 'elk';
    // When subnets are hidden, render a flattened variant. The original
    // DOT is kept around so toggleSubnets can re-mount with the clustered
    // view without callers having to supply DOT a second time.
    const renderedDot =
      subnetsMode === 'hide' ? flattenClusters(dotSource) : dotSource;
    svg = useElk
      ? await renderModule.renderDotToSvgWithElkLayout(renderedDot)
      : await renderModule.renderDotToSvg(renderedDot);
    container.innerHTML = '';
    container.appendChild(svg);
  }
  // Tag the host so the canonical CSS (which scopes to .libpetri-viewer)
  // applies even when the consumer didn't wrap us in a .petrinet-diagram.
  container.classList.add('libpetri-viewer');

  const panzoomInstance = attachPanzoom(svg, opts.panzoom);
  const clusters = discoverClusters(svg);
  paintClusterBorders(clusters);
  const layoutMode = opts.layout ?? 'elk';
  if (layoutMode === 'elk') {
    tagReplicas(svg);
    annotateSvgForC0(svg);
  }

  const collapsedPrefixes = new Set<string>();
  let activeFilter: string | null = null;
  let highlightedNodeId: string | null = null;
  let disposed = false;

  // Chrome elements (created lazily; only when chrome:true is requested).
  // Re-rendering through the same handle does not duplicate them.
  let chromeRoot: HTMLElement | null = null;
  let sidebarHandle: SidebarHandle | null = null;
  let highlightModeEnabled = true;

  function ensureChrome(): void {
    if (!opts.chrome) return;
    if (chromeRoot && chromeRoot.parentNode === container) return;

    // Reset + Fullscreen controls anchor top-right; the C0 sidebar
    // (top-left) replaces the legacy legend + filter strip.
    chromeRoot = document.createElement('div');
    chromeRoot.className = 'libpetri-viewer-chrome';
    chromeRoot.style.position = 'absolute';
    chromeRoot.style.inset = '0';
    chromeRoot.style.pointerEvents = 'none';

    const controls = document.createElement('div');
    controls.className = 'diagram-controls';
    controls.style.pointerEvents = 'auto';
    const resetBtn = document.createElement('button');
    resetBtn.type = 'button';
    resetBtn.className = 'diagram-btn btn-reset';
    resetBtn.title = 'Reset view';
    resetBtn.textContent = 'Reset';
    resetBtn.addEventListener('click', () => handle.fit());
    const fsBtn = document.createElement('button');
    fsBtn.type = 'button';
    fsBtn.className = 'diagram-btn btn-fullscreen';
    fsBtn.title = 'Toggle fullscreen';
    fsBtn.textContent = 'Fullscreen';
    fsBtn.addEventListener('click', () => toggleFullscreen(container, fsBtn));
    // Subnet view toggle: hidden in pre-rendered-SVG mode (no DOT to
    // re-render against). Button label describes the action — what
    // clicking it will do, not the current state.
    const subnetsBtn = document.createElement('button');
    subnetsBtn.type = 'button';
    subnetsBtn.className = 'diagram-btn btn-subnets';
    subnetsBtn.title =
      subnetsMode === 'show' ? 'Hide subnet groupings' : 'Show subnet groupings';
    subnetsBtn.textContent = subnetsMode === 'show' ? 'Flat view' : 'Subnets view';
    if (dotSource == null) {
      subnetsBtn.disabled = true;
      subnetsBtn.title = 'Subnet toggle unavailable for pre-rendered SVG';
    }
    subnetsBtn.addEventListener('click', () => {
      void handle.toggleSubnets();
    });
    controls.appendChild(subnetsBtn);
    controls.appendChild(resetBtn);
    controls.appendChild(fsBtn);
    chromeRoot.appendChild(controls);

    if (getComputedStyle(container).position === 'static') {
      container.style.position = 'relative';
    }
    container.appendChild(chromeRoot);

    // The cluster-chip sidebar is the C0 chrome — only mount when
    // there's a renderable layout and at least one cluster to show.
    // In flat (subnets: 'hide') mode the SVG has no clusters by
    // construction; the explicit gate keeps the intent obvious.
    if (layoutMode === 'elk' && subnetsMode === 'show' && clusters.size > 0) {
      sidebarHandle = mountSidebar(container, clusters, {
        onVisibilityChange: (state) => handle.setVisibility(state),
        onHighlightModeChange: (enabled) => {
          highlightModeEnabled = enabled;
          if (!enabled) handle.highlight(null);
        },
      });
    }
  }

  // In-page lightbox fullscreen: toggle a CSS class on the host and
  // re-fit. We deliberately don't invoke the native Fullscreen API —
  // users want the diagram to expand inside the page, not yank the
  // browser into OS-level fullscreen.
  function toggleFullscreen(host: HTMLElement, btn: HTMLButtonElement): void {
    const isFs = host.classList.toggle('diagram-fullscreen');
    btn.textContent = isFs ? 'Exit fullscreen' : 'Fullscreen';
    requestAnimationFrame(() => handle.fit());
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
    get subnets() {
      return subnetsMode;
    },
    setSubnets(mode: SubnetVisibility): Promise<ViewerHandle> {
      // Re-mount via the canonical path so all teardown + state preservation
      // (collapse set, filter) runs through the same code as external
      // re-renders. The original dotSource is reused — pre-rendered SVG
      // mode (dotSource === null) can't toggle and is a no-op resolve.
      if (dotSource == null) return Promise.resolve(handle);
      if (mode === subnetsMode) return Promise.resolve(handle);
      return mount(dotSource, container, {
        ...opts,
        previousHandle: handle,
        subnets: mode,
      }).then((next) => {
        container.dispatchEvent(
          new CustomEvent('libpetri-viewer:remount', {
            bubbles: true,
            detail: { handle: next, subnets: mode },
          }),
        );
        return next;
      });
    },
    toggleSubnets(): Promise<ViewerHandle> {
      return handle.setSubnets(subnetsMode === 'show' ? 'hide' : 'show');
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
    fit(): void {
      if (disposed) return;
      try {
        // With the host CSS-sized and the SVG forced to width/height: 100%
        // (see .petrinet-diagram-viewer rules in viewer.css), the browser
        // auto-fits viewBox content via preserveAspectRatio="xMidYMid meet".
        // "Fit" is therefore the panzoom identity transform — no math needed.
        panzoomInstance.zoomAbs(0, 0, 1);
        panzoomInstance.moveTo(0, 0);
      } catch {
        // panzoom internals can throw if the element was detached; ignore.
      }
    },
    isInsideCollapsedCluster(graphId: string): boolean {
      return overlayIsInsideCollapsedCluster(svg, clusters, collapsedPrefixes, graphId);
    },
    get highlightedNodeId() {
      return highlightedNodeId;
    },
    highlight(nodeId: string | null): void {
      if (disposed) return;
      if (layoutMode !== 'elk') return;
      highlightedNodeId = nodeId;
      applyHighlight(svg, nodeId);
    },
    setVisibility(state: VisibilityState): void {
      if (disposed) return;
      if (layoutMode !== 'elk') return;
      applyVisibility(svg, state);
    },
    dispose(): void {
      if (disposed) return;
      disposed = true;
      try {
        panzoomInstance.dispose();
      } catch {
        // ignore
      }
      sidebarHandle?.dispose();
      sidebarHandle = null;
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

  // C0 click-to-highlight: clicking a node highlights it + every copy of
  // the same logical place. Clicking the SVG background (or the already-
  // highlighted node) clears. The sidebar's "Click node → highlight"
  // toggle gates the binding via `highlightModeEnabled`.
  if (layoutMode === 'elk') {
    svg.addEventListener('click', (ev) => {
      if (!highlightModeEnabled) return;
      const target = ev.target;
      if (!(target instanceof Element)) return;
      const nodeG = target.closest('g.node') as SVGGElement | null;
      if (!nodeG) {
        handle.highlight(null);
        return;
      }
      const id = nodeG.getAttribute('data-id');
      if (!id) return;
      handle.highlight(id === highlightedNodeId ? null : id);
    });
  }

  ensureChrome();

  // Default state: fit-to-host. Huge diagrams shouldn't mount at 1:1
  // (the user only sees the top-left corner). Deferred a frame so the
  // SVG has been laid out before getBBox + clientWidth/Height reads.
  requestAnimationFrame(() => handle.fit());

  return handle;
}
