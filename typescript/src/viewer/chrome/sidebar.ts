/**
 * C0 cluster-chip sidebar. Replaces the previous top-left legend +
 * bottom filter strip with a single left-docked panel:
 *
 *  - Cluster chips (click = toggle; shift-click = isolate to just this;
 *    ctrl/cmd-click = add/remove from selection)
 *  - "show all" / "hide all" buttons
 *  - Shared-places toggle (orphan / cross-cluster places on/off)
 *  - Highlight-mode toggle (click-node-to-highlight on/off)
 *  - Inline legend explaining the ⇄ glyph
 *
 * Mounted from {@link import('../index.js').mount} when `chrome: true`.
 * Lives inside the viewer container as an `aside` so it travels with the
 * container into fullscreen.
 *
 * @module viewer/chrome/sidebar
 */

import type { ClusterDescriptor } from '../cluster-overlay.js';
import type { VisibilityState } from '../visibility.js';

export interface SidebarCallbacks {
  /**
   * Fired whenever the visibility state changes (chip click, show/hide all,
   * or orphan toggle). Caller forwards to `handle.setVisibility(state)`.
   */
  readonly onVisibilityChange: (state: VisibilityState) => void;
  /**
   * Fired when the user toggles highlight mode off, so the caller can
   * clear any active highlight via `handle.highlight(null)`.
   */
  readonly onHighlightModeChange: (enabled: boolean) => void;
}

export interface SidebarHandle {
  /** The root `<aside>` element appended to the container. */
  readonly root: HTMLElement;
  /** Tear down listeners and remove the sidebar from the DOM. */
  dispose(): void;
}

const SIDEBAR_CLASS = 'libpetri-sidebar';
const CHIP_CLASS = 'libpetri-sidebar-chip';
const CHIP_OFF_CLASS = 'is-off';

/**
 * Build + mount the sidebar inside `container`. Returns a handle the
 * caller disposes on re-mount.
 */
export function mountSidebar(
  container: HTMLElement,
  clusters: ReadonlyMap<string, ClusterDescriptor>,
  callbacks: SidebarCallbacks,
): SidebarHandle {
  const visibleClusters = new Set<string>();
  for (const prefix of clusters.keys()) visibleClusters.add(prefix);
  let includeSharedPlaces = true;
  let highlightMode = true;

  const emit = (): void => {
    callbacks.onVisibilityChange({
      visibleClusters: new Set(visibleClusters),
      includeSharedPlaces,
    });
  };

  const root = document.createElement('aside');
  root.className = SIDEBAR_CLASS;

  const title = document.createElement('h4');
  title.className = 'libpetri-sidebar-title';
  title.textContent = `Subnets (${clusters.size})`;
  root.appendChild(title);

  // Show all / hide all
  const actions = document.createElement('div');
  actions.className = 'libpetri-sidebar-actions';
  const showAll = document.createElement('button');
  showAll.type = 'button';
  showAll.textContent = 'show all';
  const hideAll = document.createElement('button');
  hideAll.type = 'button';
  hideAll.textContent = 'hide all';
  actions.appendChild(showAll);
  actions.appendChild(hideAll);
  root.appendChild(actions);

  // Shared-places toggle — hides every replica + original of a shared
  // place (anything tagged `petri-replica`) when unchecked.
  const sharedLabel = document.createElement('label');
  sharedLabel.className = 'libpetri-sidebar-checkbox';
  const sharedCb = document.createElement('input');
  sharedCb.type = 'checkbox';
  sharedCb.checked = includeSharedPlaces;
  sharedLabel.appendChild(sharedCb);
  sharedLabel.appendChild(document.createTextNode(' Shared places'));
  sharedCb.addEventListener('change', () => {
    includeSharedPlaces = sharedCb.checked;
    emit();
  });
  root.appendChild(sharedLabel);

  // Highlight-mode toggle
  const hlLabel = document.createElement('label');
  hlLabel.className = 'libpetri-sidebar-checkbox';
  const hlCb = document.createElement('input');
  hlCb.type = 'checkbox';
  hlCb.checked = highlightMode;
  hlLabel.appendChild(hlCb);
  hlLabel.appendChild(document.createTextNode(' Click node → highlight'));
  hlCb.addEventListener('change', () => {
    highlightMode = hlCb.checked;
    callbacks.onHighlightModeChange(highlightMode);
  });
  root.appendChild(hlLabel);

  // Hint
  const hint = document.createElement('div');
  hint.className = 'libpetri-sidebar-hint';
  hint.innerHTML =
    'Click chip: toggle.<br>' +
    'Shift-click: isolate.<br>' +
    'Cmd/Ctrl-click: multi-select.<br>' +
    'Click empty: clear highlight.';
  root.appendChild(hint);

  // Chips
  const chipList = document.createElement('ul');
  chipList.className = 'libpetri-sidebar-chips';
  const chipMap = new Map<string, HTMLLIElement>();
  for (const cluster of clusters.values()) {
    const li = document.createElement('li');
    li.className = CHIP_CLASS;
    li.style.borderLeftColor = cluster.color;
    li.dataset.prefix = cluster.prefix;
    const dot = document.createElement('span');
    dot.className = 'libpetri-sidebar-chip-dot';
    dot.style.background = cluster.color;
    const name = document.createElement('span');
    name.className = 'libpetri-sidebar-chip-name';
    name.textContent = cluster.prefix;
    const count = document.createElement('span');
    count.className = 'libpetri-sidebar-chip-count';
    count.textContent = String(cluster.nodeCount);
    li.appendChild(dot);
    li.appendChild(name);
    li.appendChild(count);
    li.addEventListener('click', (ev) => {
      const prefix = cluster.prefix;
      if (ev.shiftKey) {
        // Isolate to just this one — or restore "show all" if already isolated.
        const allOff = [...clusters.keys()].every(k =>
          k === prefix ? visibleClusters.has(k) : !visibleClusters.has(k),
        );
        visibleClusters.clear();
        if (allOff) for (const k of clusters.keys()) visibleClusters.add(k);
        else visibleClusters.add(prefix);
      } else if (ev.ctrlKey || ev.metaKey) {
        // Multi-select: ADD/remove. If currently "show all", start fresh.
        const anyHidden = [...clusters.keys()].some(k => !visibleClusters.has(k));
        if (!anyHidden) {
          visibleClusters.clear();
          visibleClusters.add(prefix);
        } else if (visibleClusters.has(prefix)) {
          visibleClusters.delete(prefix);
        } else {
          visibleClusters.add(prefix);
        }
      } else {
        if (visibleClusters.has(prefix)) visibleClusters.delete(prefix);
        else visibleClusters.add(prefix);
      }
      refreshChips();
      emit();
    });
    chipList.appendChild(li);
    chipMap.set(cluster.prefix, li);
  }
  root.appendChild(chipList);

  function refreshChips(): void {
    for (const [prefix, li] of chipMap) {
      li.classList.toggle(CHIP_OFF_CLASS, !visibleClusters.has(prefix));
    }
  }

  showAll.addEventListener('click', () => {
    visibleClusters.clear();
    for (const k of clusters.keys()) visibleClusters.add(k);
    includeSharedPlaces = true;
    sharedCb.checked = true;
    refreshChips();
    emit();
  });
  hideAll.addEventListener('click', () => {
    visibleClusters.clear();
    includeSharedPlaces = false;
    sharedCb.checked = false;
    refreshChips();
    emit();
  });

  container.appendChild(root);

  // Emit initial state so the caller's visibility starts in sync.
  emit();

  return {
    root,
    dispose(): void {
      if (root.parentNode === container) container.removeChild(root);
    },
  };
}
