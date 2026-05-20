/**
 * Diagram transition actions: viewer mount, SVG cache, differential highlighting.
 *
 * Rendering + cluster overlay are delegated to the canonical
 * {@link import('libpetri/viewer').mount} so this app renders identically to
 * the doclet/dev-preview/rustdoc surfaces (single source of truth).
 *
 * The debug-ui keeps its own surrounding chrome (sidebar, panels, dark theme)
 * so we pass `chrome: false` and translate the subnet sidebar's
 * `subnet:collapse` / `subnet:isolate` window events (emitted by
 * {@link import('../../dom/components/subnet-panel.js').mountSubnetPanel})
 * into `handle.collapse` / `handle.expand` / `handle.filter` calls.
 */

import { mount } from 'libpetri/viewer';
import { shared } from '../shared-state.js';
import { el } from '../../dom/elements.js';
import type { SvgNodeCache, UIState, SessionData } from '../types.js';

/** Lazily-attached, app-scoped translation of subnet sidebar events. */
let subnetListenersAttached = false;

/**
 * Render DOT string to SVG, attach panzoom, surface cluster overlay controls.
 *
 * Layout is deterministic across reloads; libpetri servers emit byte-stable DOT
 * (per spec EXP-014) and the 'dot' engine produces identical layout for identical input.
 */
export async function renderDotDiagram(dotSource: string): Promise<void> {
  const previousHandle = shared.viewerHandle;

  const handle = await mount(dotSource, el.dotDiagram, {
    previousHandle,
    chrome: false,
    subnets: shared.subnetsMode,
  });

  shared.viewerHandle = handle;
  shared.svgNodeCache = buildSvgNodeCache(handle.svg);

  attachSubnetListeners();

  el.noSession.classList.add('hidden');
}

/**
 * Flip the diagram between clustered (`'show'`) and flat one-net
 * (`'hide'`) subnet visibility.
 *
 * Re-mounts via the viewer handle (the SVG is regenerated because
 * Graphviz lays out cluster boundaries during layout), refreshes the
 * stale SVG node cache, and updates the header toggle button label.
 * Highlighting is re-applied by the caller emitting `highlightDirty`.
 */
export async function toggleSubnetMode(): Promise<void> {
  const handle = shared.viewerHandle;
  if (!handle) return;

  const next = await handle.toggleSubnets();
  shared.viewerHandle = next;
  shared.subnetsMode = next.subnets;
  shared.svgNodeCache = buildSvgNodeCache(next.svg);
  shared.prevHighlighted = { shapes: [], edges: [] };

  el.toggleSubnets.textContent = next.subnets === 'hide' ? 'Subnet View' : 'Flat View';
}

/**
 * Translate the subnet sidebar's window events (`subnet:collapse` /
 * `subnet:isolate`, dispatched by `mountSubnetPanel`) into method calls on
 * the live `shared.viewerHandle`. Both events toggle: re-firing the same
 * event reverses the action.
 *
 * Attached lazily on first render; listeners live for the lifetime of the
 * tab and operate on whichever handle is currently live in `shared`.
 */
function attachSubnetListeners(): void {
  if (subnetListenersAttached) return;
  subnetListenersAttached = true;

  window.addEventListener('subnet:collapse', (ev: Event) => {
    const detail = (ev as CustomEvent<{ prefix: string }>).detail;
    const prefix = detail?.prefix;
    if (!prefix) return;
    const handle = shared.viewerHandle;
    if (!handle) return;
    if (handle.collapsedPrefixes.has(prefix)) {
      handle.expand(prefix);
    } else {
      handle.collapse(prefix);
    }
  });

  window.addEventListener('subnet:isolate', (ev: Event) => {
    const detail = (ev as CustomEvent<{ prefix: string }>).detail;
    const prefix = detail?.prefix;
    if (!prefix) return;
    const handle = shared.viewerHandle;
    if (!handle) return;
    if (handle.activeFilter === prefix) {
      handle.filter(null);
    } else {
      handle.filter(prefix);
    }
  });
}

/**
 * Build SVG node cache mapping graphIds/names to elements.
 *
 * Synthetic junction nodes (j_-prefixed, per spec EXP-014) are skipped: they
 * are pure visualization scaffolding, not domain entities, and will never be
 * looked up via the place/transition `graphId` indexes used by highlighting.
 */
function buildSvgNodeCache(svg: SVGSVGElement): SvgNodeCache {
  const nodesByName = new Map<string, Element>();
  const nodesByGraphId = new Map<string, Element>();
  const edgesByGraphId = new Map<string, Element[]>();
  const allNodeShapes: Element[] = [];
  const allEdgePaths: Element[] = [];

  const nodeGroups = svg.querySelectorAll('g.node');
  for (const g of nodeGroups) {
    const title = g.querySelector('title');
    if (!title) continue;
    const graphId = title.textContent?.trim() ?? '';
    if (graphId.startsWith('j_')) continue;
    nodesByGraphId.set(graphId, g);

    const shapes = g.querySelectorAll('ellipse, polygon, rect');
    for (const s of shapes) allNodeShapes.push(s);
  }

  const edgeGroups = svg.querySelectorAll('g.edge');
  for (const g of edgeGroups) {
    const title = g.querySelector('title');
    if (!title) continue;
    const edgeId = title.textContent?.trim() ?? '';
    const parts = edgeId.split('->').map(s => s.trim());

    for (const part of parts) {
      const existing = edgesByGraphId.get(part) ?? [];
      existing.push(g);
      edgesByGraphId.set(part, existing);
    }

    const paths = g.querySelectorAll('path, polygon');
    for (const p of paths) allEdgePaths.push(p);
  }

  return { nodesByName, nodesByGraphId, edgesByGraphId, allNodeShapes, allEdgePaths };
}

/** Differential SVG highlighting based on current state. */
export function updateDiagramHighlighting(uiState: UIState, session: SessionData | null): void {
  const cache = shared.svgNodeCache;
  const handle = shared.viewerHandle;
  if (!cache || !session) return;

  // 1. Reset previously highlighted elements (differential: O(prev) not O(all))
  for (const shape of shared.prevHighlighted.shapes) {
    (shape as SVGElement).style.stroke = '';
    (shape as SVGElement).style.filter = '';
  }
  for (const edge of shared.prevHighlighted.edges) {
    (edge as SVGElement).style.filter = '';
    const paths = edge.querySelectorAll('path');
    for (const path of paths) {
      (path as SVGElement).style.stroke = '';
    }
  }

  const newShapes: Element[] = [];
  const newEdges: Element[] = [];

  // 2. Highlight places with tokens (green glow)
  for (const placeName of Object.keys(uiState.marking)) {
    const tokens = uiState.marking[placeName];
    if (!tokens || tokens.length === 0) continue;

    // Find graphId for this place name
    const placeInfo = session.structure.places.find(p => p.name === placeName);
    if (!placeInfo) continue;

    const node = cache.nodesByGraphId.get(placeInfo.graphId);
    if (!node) continue;
    // Skip nodes inside a collapsed cluster — their shapes are detached
    // from the live SVG so painting stroke/filter has no visible effect
    // and would just dirty the prevHighlighted set with stale references.
    if (handle?.isInsideCollapsedCluster(placeInfo.graphId)) continue;

    const shapes = node.querySelectorAll('ellipse, polygon, rect');
    for (const shape of shapes) {
      (shape as SVGElement).style.stroke = '#22c55e';
      (shape as SVGElement).style.filter = 'drop-shadow(0 0 4px #22c55e)';
      newShapes.push(shape);
    }
  }

  // 3. Highlight enabled transitions (yellow glow)
  for (const tName of uiState.enabledTransitions) {
    const tInfo = session.structure.transitions.find(t => t.name === tName);
    if (!tInfo) continue;

    const node = cache.nodesByGraphId.get(tInfo.graphId);
    if (!node) continue;
    if (handle?.isInsideCollapsedCluster(tInfo.graphId)) continue;

    const shapes = node.querySelectorAll('ellipse, polygon, rect');
    for (const shape of shapes) {
      (shape as SVGElement).style.stroke = '#eab308';
      (shape as SVGElement).style.filter = 'drop-shadow(0 0 4px #eab308)';
      newShapes.push(shape);
    }

    // Highlight connected edges
    const edges = cache.edgesByGraphId.get(tInfo.graphId) ?? [];
    for (const edge of edges) {
      (edge as SVGElement).style.filter = 'drop-shadow(0 0 2px #eab308)';
      newEdges.push(edge);
    }
  }

  // 4. Highlight in-flight transitions (orange glow, overrides yellow)
  for (const tName of uiState.inFlightTransitions) {
    const tInfo = session.structure.transitions.find(t => t.name === tName);
    if (!tInfo) continue;

    const node = cache.nodesByGraphId.get(tInfo.graphId);
    if (!node) continue;
    if (handle?.isInsideCollapsedCluster(tInfo.graphId)) continue;

    const shapes = node.querySelectorAll('ellipse, polygon, rect');
    for (const shape of shapes) {
      (shape as SVGElement).style.stroke = '#f97316';
      (shape as SVGElement).style.filter = 'drop-shadow(0 0 6px #f97316)';
      newShapes.push(shape);
    }

    const edges = cache.edgesByGraphId.get(tInfo.graphId) ?? [];
    for (const edge of edges) {
      (edge as SVGElement).style.filter = 'drop-shadow(0 0 3px #f97316)';
      const paths = edge.querySelectorAll('path');
      for (const path of paths) {
        (path as SVGElement).style.stroke = '#f97316';
      }
      newEdges.push(edge);
    }
  }

  shared.prevHighlighted = { shapes: newShapes, edges: newEdges };
}

/** Reset zoom on the active viewer handle. */
export function resetZoom(): void {
  shared.viewerHandle?.resetZoom();
}
