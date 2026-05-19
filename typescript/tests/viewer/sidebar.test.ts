/**
 * Tests for the C0 cluster-chip sidebar.
 *
 * @vitest-environment happy-dom
 */
import { describe, expect, it } from 'vitest';
import { mountSidebar } from '../../src/viewer/chrome/sidebar.js';
import type { ClusterDescriptor } from '../../src/viewer/cluster-overlay.js';
import type { VisibilityState } from '../../src/viewer/visibility.js';

function fakeCluster(prefix: string): ClusterDescriptor {
  // Minimal descriptor — sidebar only reads prefix, color, nodeCount.
  return {
    prefix,
    color: 'hsl(0, 60%, 45%)',
    nodeCount: 3,
    // Cast away the structural fields the sidebar doesn't touch.
  } as unknown as ClusterDescriptor;
}

function makeContainer(): HTMLElement {
  document.body.innerHTML = '';
  const c = document.createElement('div');
  document.body.appendChild(c);
  return c;
}

function trackedCallbacks(): {
  states: VisibilityState[];
  highlight: boolean[];
  fns: {
    onVisibilityChange: (s: VisibilityState) => void;
    onHighlightModeChange: (b: boolean) => void;
  };
} {
  const states: VisibilityState[] = [];
  const highlight: boolean[] = [];
  return {
    states,
    highlight,
    fns: {
      onVisibilityChange: (s) => states.push({
        visibleClusters: new Set(s.visibleClusters),
        includeSharedPlaces: s.includeSharedPlaces,
      }),
      onHighlightModeChange: (b) => highlight.push(b),
    },
  };
}

function chipFor(container: HTMLElement, prefix: string): HTMLElement {
  return container.querySelector<HTMLElement>(
    `.libpetri-sidebar-chip[data-prefix="${prefix}"]`,
  )!;
}

describe('mountSidebar', () => {
  it('plain click toggles a single chip', () => {
    const c = makeContainer();
    const clusters = new Map([
      ['alpha', fakeCluster('alpha')],
      ['beta', fakeCluster('beta')],
    ]);
    const cb = trackedCallbacks();
    mountSidebar(c, clusters, cb.fns);

    // initial emit on mount = both visible
    expect(cb.states.at(-1)?.visibleClusters).toEqual(new Set(['alpha', 'beta']));

    chipFor(c, 'alpha').click();

    expect(cb.states.at(-1)?.visibleClusters).toEqual(new Set(['beta']));
  });

  it('shift-click isolates to just one cluster; shift-click again restores all', () => {
    const c = makeContainer();
    const clusters = new Map([
      ['alpha', fakeCluster('alpha')],
      ['beta', fakeCluster('beta')],
      ['gamma', fakeCluster('gamma')],
    ]);
    const cb = trackedCallbacks();
    mountSidebar(c, clusters, cb.fns);

    chipFor(c, 'alpha').dispatchEvent(new MouseEvent('click', { shiftKey: true }));
    expect(cb.states.at(-1)?.visibleClusters).toEqual(new Set(['alpha']));

    chipFor(c, 'alpha').dispatchEvent(new MouseEvent('click', { shiftKey: true }));
    expect(cb.states.at(-1)?.visibleClusters).toEqual(new Set(['alpha', 'beta', 'gamma']));
  });

  it('ctrl-click adds when something is already hidden, starts fresh otherwise', () => {
    const c = makeContainer();
    const clusters = new Map([
      ['alpha', fakeCluster('alpha')],
      ['beta', fakeCluster('beta')],
    ]);
    const cb = trackedCallbacks();
    mountSidebar(c, clusters, cb.fns);

    // From "show all", ctrl-click on alpha → start fresh with just alpha
    chipFor(c, 'alpha').dispatchEvent(new MouseEvent('click', { ctrlKey: true }));
    expect(cb.states.at(-1)?.visibleClusters).toEqual(new Set(['alpha']));

    // Now ctrl-click beta → add to selection (something is hidden, so toggle)
    chipFor(c, 'beta').dispatchEvent(new MouseEvent('click', { ctrlKey: true }));
    expect(cb.states.at(-1)?.visibleClusters).toEqual(new Set(['alpha', 'beta']));

    // ctrl-click alpha when all visible → starts fresh with just alpha
    // (matches v3 — once everything is back on, ctrl-click resets selection)
    chipFor(c, 'alpha').dispatchEvent(new MouseEvent('click', { ctrlKey: true }));
    expect(cb.states.at(-1)?.visibleClusters).toEqual(new Set(['alpha']));
  });

  it('highlight-mode toggle fires onHighlightModeChange', () => {
    const c = makeContainer();
    const clusters = new Map([['alpha', fakeCluster('alpha')]]);
    const cb = trackedCallbacks();
    mountSidebar(c, clusters, cb.fns);

    const hlCheckbox = c.querySelectorAll<HTMLInputElement>(
      '.libpetri-sidebar-checkbox input',
    )[1]!;
    hlCheckbox.checked = false;
    hlCheckbox.dispatchEvent(new Event('change'));

    expect(cb.highlight.at(-1)).toBe(false);
  });

  it('dispose removes the sidebar from the container', () => {
    const c = makeContainer();
    const clusters = new Map([['alpha', fakeCluster('alpha')]]);
    const cb = trackedCallbacks();
    const h = mountSidebar(c, clusters, cb.fns);

    expect(c.querySelector('.libpetri-sidebar')).not.toBeNull();
    h.dispose();
    expect(c.querySelector('.libpetri-sidebar')).toBeNull();
  });
});
