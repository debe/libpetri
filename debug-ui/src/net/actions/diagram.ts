/**
 * Diagram transition actions: viz.js rendering, panzoom init, SVG cache, differential highlighting.
 */

import { instance as vizInstance } from '@viz-js/viz';
import panzoom from 'panzoom';
import { shared } from '../shared-state.js';
import { el } from '../../dom/elements.js';
import type { SvgNodeCache, UIState, SessionData } from '../types.js';

let vizPromise: Promise<Awaited<ReturnType<typeof vizInstance>>> | null = null;

function getViz() {
  if (!vizPromise) vizPromise = vizInstance();
  return vizPromise;
}

/** Render DOT string to SVG and initialize panzoom. */
export async function renderDotDiagram(dotSource: string): Promise<void> {
  const viz = await getViz();
  const svgElement = viz.renderSVGElement(dotSource);

  // Replace diagram content
  const container = el.dotDiagram;
  container.innerHTML = '';
  container.appendChild(svgElement);

  // Destroy previous panzoom
  if (shared.panzoomInstance) {
    shared.panzoomInstance.dispose();
  }

  // Init panzoom
  shared.panzoomInstance = panzoom(svgElement, {
    smoothScroll: false,
    zoomDoubleClickSpeed: 1,
  });

  // Build SVG node cache for O(1) lookups
  shared.svgNodeCache = buildSvgNodeCache(svgElement);

  el.noSession.classList.add('hidden');
}

/** Build SVG node cache mapping graphIds/names to elements. */
function buildSvgNodeCache(svg: SVGSVGElement): SvgNodeCache {
  const nodesByName = new Map<string, Element>();
  const nodesByGraphId = new Map<string, Element>();
  const edgesByGraphId = new Map<string, Element[]>();
  const allNodeShapes: Element[] = [];
  const allEdgePaths: Element[] = [];

  // Nodes: <g class="node"> with <title>graphId</title>
  const nodeGroups = svg.querySelectorAll('g.node');
  for (const g of nodeGroups) {
    const title = g.querySelector('title');
    if (!title) continue;
    const graphId = title.textContent?.trim() ?? '';
    nodesByGraphId.set(graphId, g);

    // Collect shapes (ellipse, polygon, rect)
    const shapes = g.querySelectorAll('ellipse, polygon, rect');
    for (const s of shapes) allNodeShapes.push(s);
  }

  // Edges: <g class="edge"> with <title>from->to</title>
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

/** Reset zoom on panzoom instance. */
export function resetZoom(): void {
  if (shared.panzoomInstance) {
    shared.panzoomInstance.zoomAbs(0, 0, 1);
    shared.panzoomInstance.moveTo(0, 0);
  }
}
