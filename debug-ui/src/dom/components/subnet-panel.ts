/**
 * Sidebar component listing composed `SubnetInstance`s reported by the debug
 * server per `spec/11-modular-composition.md` MOD-041. Each card shows the
 * instance prefix, optional def name and parent prefix, and per-instance
 * controls: Collapse (hide internals in the diagram), Isolate (dim everything
 * outside this prefix), and Breakpoint (set/clear an instance-level breakpoint
 * that fires on any prefixed transition).
 *
 * Collapse and Isolate are surfaced as `CustomEvent`s dispatched on `window`
 * (`subnet:collapse:<prefix>`, `subnet:isolate:<prefix>`) so the diagram-side
 * SVG manipulation (task #26) can listen without coupling. Breakpoint actions
 * are dispatched via the supplied `onToggleBreakpoint` callback so this module
 * stays independent of the executor and breakpoints state container.
 */

import type { SubnetInstanceInfo } from '../../protocol/index.js';

/**
 * Callbacks the host wires up so the panel stays decoupled from the Petri
 * executor and the breakpoints store. {@link isBreakpointSet} drives the
 * breakpoint toggle's checked state on each render.
 */
export interface SubnetPanelOptions {
  readonly onToggleBreakpoint: (prefix: string, on: boolean) => void;
  readonly isBreakpointSet: (prefix: string) => boolean;
  readonly onSelectFilter?: (prefix: string) => void;
}

const COLLAPSE_EVENT_PREFIX = 'subnet:collapse:';
const ISOLATE_EVENT_PREFIX = 'subnet:isolate:';

/**
 * Render the panel into `container`. Idempotent — re-rendering replaces the
 * previous DOM. Empty `instances` produces a small placeholder so the panel
 * does not visually disappear.
 */
export function mountSubnetPanel(
  container: HTMLElement,
  instances: readonly SubnetInstanceInfo[],
  opts: SubnetPanelOptions,
): void {
  container.innerHTML = '';
  container.classList.add('subnet-panel');

  const header = document.createElement('div');
  header.className = 'subnet-panel-header';
  header.innerHTML = `
    <h2 class="text-sm font-semibold text-gray-200">Subnet Instances</h2>
    <span class="text-xs text-gray-500">${instances.length}</span>
  `;
  container.appendChild(header);

  if (instances.length === 0) {
    const empty = document.createElement('div');
    empty.className = 'subnet-panel-empty text-xs text-gray-500 italic px-3 py-4';
    empty.textContent = 'No subnets in current net.';
    container.appendChild(empty);
    return;
  }

  const list = document.createElement('div');
  list.className = 'subnet-panel-list';
  for (const inst of instances) {
    list.appendChild(renderCard(inst, opts));
  }
  container.appendChild(list);
}

function renderCard(inst: SubnetInstanceInfo, opts: SubnetPanelOptions): HTMLElement {
  const card = document.createElement('div');
  card.className = 'subnet-card';
  card.dataset['prefix'] = inst.prefix;

  // Header row: prefix + def name + parent badge
  const head = document.createElement('div');
  head.className = 'subnet-card-head';

  const prefixEl = document.createElement('div');
  prefixEl.className = 'subnet-card-prefix';
  prefixEl.textContent = inst.prefix;
  head.appendChild(prefixEl);

  if (inst.defName) {
    const def = document.createElement('div');
    def.className = 'subnet-card-defname';
    def.textContent = inst.defName;
    head.appendChild(def);
  }

  if (inst.parentPrefix) {
    const parent = document.createElement('span');
    parent.className = 'subnet-card-parent-badge';
    parent.title = `Nested in ${inst.parentPrefix}`;
    parent.textContent = `↳ ${inst.parentPrefix}`;
    head.appendChild(parent);
  }
  card.appendChild(head);

  // Exposed places section
  if (inst.exposedPlaceNames.length > 0) {
    card.appendChild(renderBadgeGroup(
      'Exposed places',
      inst.exposedPlaceNames,
      'subnet-badge-place',
    ));
  }

  // Transitions section
  if (inst.transitionNames.length > 0) {
    card.appendChild(renderBadgeGroup(
      'Transitions',
      inst.transitionNames,
      'subnet-badge-transition',
    ));
  }

  // Action toggles
  const actions = document.createElement('div');
  actions.className = 'subnet-card-actions';

  actions.appendChild(makeToggle('Collapse', 'collapse', false, () => {
    dispatchPrefixed(COLLAPSE_EVENT_PREFIX, inst.prefix);
  }));

  actions.appendChild(makeToggle('Show only', 'isolate', false, () => {
    dispatchPrefixed(ISOLATE_EVENT_PREFIX, inst.prefix);
  }));

  const bpOn = opts.isBreakpointSet(inst.prefix);
  actions.appendChild(makeToggle('Breakpoint', 'breakpoint', bpOn, () => {
    opts.onToggleBreakpoint(inst.prefix, !bpOn);
  }));

  if (opts.onSelectFilter) {
    actions.appendChild(makeToggle('Filter log', 'filter', false, () => {
      opts.onSelectFilter!(inst.prefix);
    }));
  }
  card.appendChild(actions);

  return card;
}

function renderBadgeGroup(label: string, names: readonly string[], badgeClass: string): HTMLElement {
  const group = document.createElement('div');
  group.className = 'subnet-card-group';

  const lbl = document.createElement('div');
  lbl.className = 'subnet-card-group-label';
  lbl.textContent = `${label} (${names.length})`;
  group.appendChild(lbl);

  const wrap = document.createElement('div');
  wrap.className = 'subnet-card-badges';
  for (const name of names) {
    const badge = document.createElement('span');
    badge.className = `subnet-badge ${badgeClass}`;
    // Strip the instance prefix off for visual brevity, e.g. `buf1/in` -> `in`
    const display = stripPrefix(name);
    badge.textContent = display;
    badge.title = name;
    wrap.appendChild(badge);
  }
  group.appendChild(wrap);
  return group;
}

function stripPrefix(name: string): string {
  const slash = name.lastIndexOf('/');
  return slash >= 0 ? name.slice(slash + 1) : name;
}

function makeToggle(label: string, kind: string, on: boolean, onClick: () => void): HTMLElement {
  const btn = document.createElement('button');
  btn.type = 'button';
  btn.className = `subnet-toggle subnet-toggle-${kind}` + (on ? ' subnet-toggle-on' : '');
  btn.dataset['toggle'] = kind;
  btn.setAttribute('aria-pressed', on ? 'true' : 'false');
  btn.textContent = label;
  btn.addEventListener('click', (e) => {
    e.stopPropagation();
    onClick();
  });
  return btn;
}

function dispatchPrefixed(eventPrefix: string, instancePrefix: string): void {
  const ev = new CustomEvent(eventPrefix + instancePrefix, {
    detail: { prefix: instancePrefix },
    bubbles: false,
  });
  window.dispatchEvent(ev);
  // Also dispatch the unscoped event with detail so general listeners can pick it up.
  const generic = new CustomEvent(eventPrefix.slice(0, -1), {
    detail: { prefix: instancePrefix },
    bubbles: false,
  });
  window.dispatchEvent(generic);
}
