/**
 * Viewer test setup: stubs @viz-js/viz and panzoom so the viewer module
 * runs under happy-dom without the heavy wasm payload + without panzoom's
 * RequestAnimationFrame churn.
 *
 * Each test builds its own SVG fragment via document.createElementNS and
 * the viz mock simply returns whatever the test put in `mockVizSvg()`.
 */
import { vi } from 'vitest';

let mockSvgFactory: () => SVGSVGElement = () => {
  const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  svg.innerHTML = '<g id="graph0"><title>empty</title></g>';
  return svg;
};

export function setMockSvgFactory(fn: () => SVGSVGElement): void {
  mockSvgFactory = fn;
}

vi.mock('@viz-js/viz', () => ({
  instance: () => Promise.resolve({
    renderSVGElement: (_dot: string) => mockSvgFactory(),
  }),
}));

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
