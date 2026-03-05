/**
 * Shared test setup: creates minimal DOM with all required element IDs,
 * and mocks external modules (@viz-js/viz, panzoom).
 */
import { vi, beforeEach, afterEach } from 'vitest';

// Mock @viz-js/viz before any imports that use it
vi.mock('@viz-js/viz', () => ({
  instance: () => Promise.resolve({
    renderSVGElement: (_dot: string) => {
      const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
      svg.innerHTML = '<g id="graph0"><title>test</title></g>';
      return svg;
    },
  }),
}));

// Mock panzoom
vi.mock('panzoom', () => ({
  default: () => ({
    dispose: () => {},
    zoomAbs: () => {},
    moveTo: () => {},
    getTransform: () => ({ x: 0, y: 0, scale: 1 }),
    on: () => {},
    off: () => {},
  }),
}));

/** All element IDs needed by initElements(). */
const ELEMENT_IDS = [
  'status-dot', 'status-text',
  'session-select', 'refresh-sessions', 'reset-zoom',
  'diagram-container', 'dot-diagram', 'no-session',
  'marking-inspector', 'token-inspector',
  'breakpoint-list', 'add-breakpoint',
  'breakpoint-form', 'bp-type', 'bp-target', 'bp-save', 'bp-cancel',
  'event-log', 'event-count', 'clear-events', 'jump-to-latest',
  'filter-event-type', 'filter-transition', 'filter-place',
  'apply-filter', 'clear-filter',
  'search-input', 'search-results', 'search-prev', 'search-next', 'search-clear',
  'btn-restart', 'btn-step-back', 'btn-pause',
  'icon-pause', 'icon-play',
  'btn-step-forward', 'btn-run-to-end',
  'timeline-slider', 'timeline-position',
  'mode-select',
  'diagram-context-menu', 'ctx-menu-header', 'ctx-menu-inspect',
  'ctx-bp-place-options', 'ctx-bp-transition-options',
  'value-modal', 'modal-title', 'modal-subtitle', 'modal-copy', 'modal-close', 'modal-json',
  'transition-options', 'place-options',
];

/** Create all required DOM elements. */
export function setupDOM(): void {
  for (const id of ELEMENT_IDS) {
    if (document.getElementById(id)) continue;
    let tag = 'div';
    if (id.startsWith('btn-') || id.endsWith('-sessions') || id === 'reset-zoom'
      || id === 'add-breakpoint' || id.startsWith('bp-save') || id.startsWith('bp-cancel')
      || id === 'apply-filter' || id === 'clear-filter'
      || id === 'search-prev' || id === 'search-next' || id === 'search-clear'
      || id === 'jump-to-latest' || id === 'modal-copy' || id === 'modal-close') {
      tag = 'button';
    } else if (id === 'session-select' || id === 'filter-event-type' || id === 'mode-select' || id === 'bp-type') {
      tag = 'select';
    } else if (id === 'filter-transition' || id === 'filter-place' || id === 'bp-target'
      || id === 'search-input' || id === 'timeline-slider') {
      tag = 'input';
    } else if (id === 'transition-options' || id === 'place-options') {
      tag = 'datalist';
    }
    const el = document.createElement(tag);
    el.id = id;
    document.body.appendChild(el);
  }
}

/** Remove all created DOM elements. */
export function cleanupDOM(): void {
  for (const id of ELEMENT_IDS) {
    document.getElementById(id)?.remove();
  }
}

// Auto-setup/cleanup for all test files (skip when no DOM, e.g. node environment)
beforeEach(() => {
  if (typeof document !== 'undefined') setupDOM();
});

afterEach(() => {
  if (typeof document !== 'undefined') cleanupDOM();
});
