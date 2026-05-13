import { describe, it, expect, vi, beforeEach } from 'vitest';
import { mountSubnetPanel } from '../../src/dom/components/subnet-panel.js';
import type { SubnetInstanceInfo } from '../../src/protocol/index.js';

function makeInstance(overrides: Partial<SubnetInstanceInfo> = {}): SubnetInstanceInfo {
  return {
    prefix: 'buf1',
    defName: 'BoundedBuffer',
    transitionNames: ['buf1/produce', 'buf1/consume'],
    exposedPlaceNames: ['buf1/in', 'buf1/out'],
    ...overrides,
  };
}

function makeContainer(): HTMLElement {
  const el = document.createElement('aside');
  document.body.appendChild(el);
  return el;
}

const noopOpts = {
  onToggleBreakpoint: () => {},
  isBreakpointSet: () => false,
};

describe('mountSubnetPanel', () => {
  beforeEach(() => {
    document.body.innerHTML = '';
  });

  it('panel_emptyInstances_showsPlaceholder', () => {
    const container = makeContainer();
    mountSubnetPanel(container, [], noopOpts);

    const empty = container.querySelector('.subnet-panel-empty');
    expect(empty).not.toBeNull();
    expect(empty!.textContent).toContain('No subnets');
    // Header still present
    expect(container.querySelector('.subnet-panel-header')).not.toBeNull();
  });

  it('panel_singleInstance_rendersCard', () => {
    const container = makeContainer();
    mountSubnetPanel(container, [makeInstance()], noopOpts);

    const card = container.querySelector('.subnet-card');
    expect(card).not.toBeNull();
    expect(card!.getAttribute('data-prefix')).toBe('buf1');

    // Prefix and def name visible
    expect(container.querySelector('.subnet-card-prefix')!.textContent).toBe('buf1');
    expect(container.querySelector('.subnet-card-defname')!.textContent).toBe('BoundedBuffer');

    // Place + transition badges rendered
    const placeBadges = container.querySelectorAll('.subnet-badge-place');
    const transitionBadges = container.querySelectorAll('.subnet-badge-transition');
    expect(placeBadges.length).toBe(2);
    expect(transitionBadges.length).toBe(2);
    // Badges strip the prefix for display
    expect([...placeBadges].map(b => b.textContent)).toEqual(['in', 'out']);
    expect([...transitionBadges].map(b => b.textContent)).toEqual(['produce', 'consume']);
  });

  it('panel_nestedInstance_showsParentBadge', () => {
    const container = makeContainer();
    mountSubnetPanel(container, [makeInstance({
      prefix: 'outer/inner',
      parentPrefix: 'outer',
    })], noopOpts);

    const parent = container.querySelector('.subnet-card-parent-badge');
    expect(parent).not.toBeNull();
    expect(parent!.textContent).toContain('outer');
  });

  it('panel_collapseToggle_dispatchesEvent', () => {
    const container = makeContainer();
    mountSubnetPanel(container, [makeInstance()], noopOpts);

    const handler = vi.fn();
    window.addEventListener('subnet:collapse:buf1', handler as EventListener);

    const btn = container.querySelector('.subnet-toggle-collapse') as HTMLButtonElement;
    btn.click();

    expect(handler).toHaveBeenCalledOnce();
    const ev = handler.mock.calls[0]![0] as CustomEvent;
    expect(ev.detail).toEqual({ prefix: 'buf1' });
  });

  it('panel_isolateToggle_dispatchesEvent', () => {
    const container = makeContainer();
    mountSubnetPanel(container, [makeInstance()], noopOpts);

    const handler = vi.fn();
    window.addEventListener('subnet:isolate:buf1', handler as EventListener);

    const btn = container.querySelector('.subnet-toggle-isolate') as HTMLButtonElement;
    btn.click();

    expect(handler).toHaveBeenCalledOnce();
    const ev = handler.mock.calls[0]![0] as CustomEvent;
    expect(ev.detail.prefix).toBe('buf1');
  });

  it('panel_breakpointToggle_callsBreakpointAction', () => {
    const container = makeContainer();
    const onToggleBreakpoint = vi.fn();
    mountSubnetPanel(container, [makeInstance()], {
      onToggleBreakpoint,
      isBreakpointSet: () => false,
    });

    const btn = container.querySelector('.subnet-toggle-breakpoint') as HTMLButtonElement;
    btn.click();

    expect(onToggleBreakpoint).toHaveBeenCalledWith('buf1', true);
  });

  it('panel_breakpointToggle_alreadySet_clears', () => {
    const container = makeContainer();
    const onToggleBreakpoint = vi.fn();
    mountSubnetPanel(container, [makeInstance()], {
      onToggleBreakpoint,
      isBreakpointSet: () => true,
    });

    const btn = container.querySelector('.subnet-toggle-breakpoint') as HTMLButtonElement;
    expect(btn.getAttribute('aria-pressed')).toBe('true');
    expect(btn.classList.contains('subnet-toggle-on')).toBe(true);

    btn.click();
    expect(onToggleBreakpoint).toHaveBeenCalledWith('buf1', false);
  });

  it('panel_filterToggle_dispatchesCallback', () => {
    const container = makeContainer();
    const onSelectFilter = vi.fn();
    mountSubnetPanel(container, [makeInstance()], {
      onToggleBreakpoint: () => {},
      isBreakpointSet: () => false,
      onSelectFilter,
    });
    (container.querySelector('.subnet-toggle-filter') as HTMLButtonElement).click();
    expect(onSelectFilter).toHaveBeenCalledWith('buf1');
  });

  it('panel_isIdempotent_replacesPrevious', () => {
    const container = makeContainer();
    mountSubnetPanel(container, [makeInstance()], noopOpts);
    expect(container.querySelectorAll('.subnet-card').length).toBe(1);

    mountSubnetPanel(container, [makeInstance({ prefix: 'a' }), makeInstance({ prefix: 'b' })], noopOpts);
    expect(container.querySelectorAll('.subnet-card').length).toBe(2);
    const prefixes = [...container.querySelectorAll('.subnet-card')].map(c => c.getAttribute('data-prefix'));
    expect(prefixes).toEqual(['a', 'b']);
  });
});
