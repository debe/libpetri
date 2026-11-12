/**
 * The diagram search in the debug-ui header: the box, the counter and the ‹ › buttons drive
 * the viewer handle's search and mirror its state back.
 */
import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import type { ViewerHandle } from 'libpetri/viewer';
import { el } from '../../src/dom/elements.js';
import { bindDomEvents } from '../../src/dom/bindings.js';
import { shared } from '../../src/net/shared-state.js';
import { startNet, settle, type RunningNet } from '../net-harness.js';

const HITS: Record<string, number> = { order: 3, budget: 1 };

/** A handle whose search finds `HITS[query]` hits and steps with wrap-around. */
function fakeHandle() {
  let state = { query: '', index: -1, count: 0 };
  const step = (delta: number) => {
    if (state.count > 0) state = { ...state, index: (state.index + delta + state.count) % state.count };
  };
  return {
    search: vi.fn((query: string) => {
      const q = query.trim();
      const count = q === '' ? 0 : HITS[q] ?? 0;
      state = { query: q, index: count > 0 ? 0 : -1, count };
      return count;
    }),
    searchNext: vi.fn(() => step(1)),
    searchPrev: vi.fn(() => step(-1)),
    clearSearch: vi.fn(() => { state = { query: '', index: -1, count: 0 }; }),
    get searchState() { return state; },
  };
}

describe('debug-ui diagram search', () => {
  let n: RunningNet;
  let handle: ReturnType<typeof fakeHandle>;

  beforeEach(() => {
    n = startNet();
    bindDomEvents(n.executor);
    handle = fakeHandle();
    shared.viewerHandle = handle as unknown as ViewerHandle;
  });

  afterEach(() => {
    n.close();
  });

  const key = (k: string, shiftKey = false) =>
    el.diagramSearch.dispatchEvent(new KeyboardEvent('keydown', { key: k, shiftKey, bubbles: true }));

  it('Enter runs the typed query at once, then steps through the hits', () => {
    el.diagramSearch.value = 'order';
    key('Enter');
    expect(handle.search).toHaveBeenCalledWith('order');
    expect(el.diagramSearchCount.textContent).toBe('1/3');
    expect(el.diagramSearchPrev.disabled).toBe(false);
    expect(el.diagramSearchNext.disabled).toBe(false);

    key('Enter');
    expect(el.diagramSearchCount.textContent).toBe('2/3');
    key('Enter', true);
    key('Enter', true);
    expect(el.diagramSearchCount.textContent).toBe('3/3');
    expect(handle.search).toHaveBeenCalledTimes(1);
  });

  it('typing searches after the debounce', async () => {
    el.diagramSearch.value = 'budget';
    el.diagramSearch.dispatchEvent(new Event('input'));
    expect(handle.search).not.toHaveBeenCalled();
    await settle(200);
    expect(handle.search).toHaveBeenCalledWith('budget');
    expect(el.diagramSearchCount.textContent).toBe('1/1');
  });

  it('the ‹ › buttons step with wrap-around', () => {
    el.diagramSearch.value = 'order';
    key('Enter');
    el.diagramSearchPrev.click();
    expect(el.diagramSearchCount.textContent).toBe('3/3');
    el.diagramSearchNext.click();
    expect(el.diagramSearchCount.textContent).toBe('1/3');
  });

  it('no hits shows 0/0 in red and disables the buttons', () => {
    el.diagramSearch.value = 'nothing';
    key('Enter');
    expect(el.diagramSearchCount.textContent).toBe('0/0');
    expect(el.diagramSearchCount.classList.contains('text-red-400')).toBe(true);
    expect(el.diagramSearchPrev.disabled).toBe(true);
    expect(el.diagramSearchNext.disabled).toBe(true);
  });

  it('Esc clears the box, the search and the counter', () => {
    el.diagramSearch.value = 'order';
    key('Enter');
    key('Escape');
    expect(el.diagramSearch.value).toBe('');
    expect(handle.clearSearch).toHaveBeenCalled();
    expect(el.diagramSearchCount.textContent).toBe('');
    expect(el.diagramSearchCount.classList.contains('text-red-400')).toBe(false);
    expect(el.diagramSearchNext.disabled).toBe(true);
  });
});
