/**
 * Event log transition actions: virtual scroll rendering.
 */

import { el } from '../../dom/elements.js';
import { shared } from '../shared-state.js';
import type { UIState, FilterState } from '../types.js';
import type { NetEventInfo } from '../../protocol/index.js';

const ITEM_HEIGHT = 72;
const OVERSCAN = 10;

/** Render only visible events using virtual scrolling (spacer sandwich pattern). */
export function renderVisibleEvents(uiState: UIState, filterState: FilterState): void {
  const container = el.eventLog;
  const events = uiState.events;
  const totalEvents = uiState.eventIndex;

  // Compute filtered indices
  const indices = filterState.filteredIndices ?? buildFilteredIndices(events, filterState, totalEvents);

  const totalFiltered = indices.length;
  const totalHeight = totalFiltered * ITEM_HEIGHT;

  // Ensure container has virtual scroll structure
  let spacerTop = container.querySelector('.spacer-top') as HTMLElement | null;
  let contentEl = container.querySelector('.virtual-content') as HTMLElement | null;
  let spacerBottom = container.querySelector('.spacer-bottom') as HTMLElement | null;

  if (!spacerTop) {
    container.innerHTML = '';
    spacerTop = document.createElement('div');
    spacerTop.className = 'spacer-top';
    contentEl = document.createElement('div');
    contentEl.className = 'virtual-content';
    spacerBottom = document.createElement('div');
    spacerBottom.className = 'spacer-bottom';
    container.appendChild(spacerTop);
    container.appendChild(contentEl);
    container.appendChild(spacerBottom);
  }

  const scrollTop = container.scrollTop;
  const viewportHeight = container.clientHeight;

  const startIdx = Math.max(0, Math.floor(scrollTop / ITEM_HEIGHT) - OVERSCAN);
  const endIdx = Math.min(totalFiltered, Math.ceil((scrollTop + viewportHeight) / ITEM_HEIGHT) + OVERSCAN);

  spacerTop.style.height = `${startIdx * ITEM_HEIGHT}px`;
  spacerBottom!.style.height = `${Math.max(0, (totalFiltered - endIdx) * ITEM_HEIGHT)}px`;

  // Render visible items
  const fragment = document.createDocumentFragment();
  for (let i = startIdx; i < endIdx; i++) {
    const eventIdx = indices[i];
    if (eventIdx === undefined || eventIdx >= events.length) continue;
    const event = events[eventIdx]!;
    fragment.appendChild(createEventElement(event, eventIdx));
  }
  contentEl!.innerHTML = '';
  contentEl!.appendChild(fragment);

  // Update event count
  el.eventCount.textContent = `${totalEvents} events`;

  // Follow mode: auto-scroll to bottom
  if (shared.virtualLog.followMode) {
    container.scrollTop = totalHeight;
  }
}

/** Build filtered index array from events. */
function buildFilteredIndices(events: readonly NetEventInfo[], filterState: FilterState, totalEvents: number): readonly number[] {
  const hasFilter = filterState.eventTypes.length > 0
    || filterState.transitionNames.length > 0
    || filterState.placeNames.length > 0;

  if (!hasFilter) {
    return Array.from({ length: Math.min(events.length, totalEvents) }, (_, i) => i);
  }

  const indices: number[] = [];
  const limit = Math.min(events.length, totalEvents);
  for (let i = 0; i < limit; i++) {
    const event = events[i]!;
    if (matchesFilter(event, filterState)) {
      indices.push(i);
    }
  }
  return indices;
}

function matchesFilter(event: NetEventInfo, filter: FilterState): boolean {
  if (filter.eventTypes.length > 0 && !filter.eventTypes.includes(event.type)) return false;
  if (filter.transitionNames.length > 0 && event.transitionName && !filter.transitionNames.includes(event.transitionName)) return false;
  if (filter.placeNames.length > 0 && event.placeName && !filter.placeNames.includes(event.placeName)) return false;
  return true;
}

/** Create a single event log entry element. */
function createEventElement(event: NetEventInfo, index: number): HTMLElement {
  const div = document.createElement('div');
  div.className = `event-entry p-2 bg-gray-800 rounded border-l-4 cursor-pointer hover:bg-gray-750 event-${event.type}`;
  if (event.type === 'LogMessage') {
    const level = (event.details?.level as string) ?? '';
    if (level === 'WARN' || level === 'ERROR') {
      div.classList.add(`level-${level}`);
    }
  }
  div.style.height = `${ITEM_HEIGHT}px`;
  div.style.boxSizing = 'border-box';
  div.dataset['eventIndex'] = String(index);

  const name = event.transitionName ?? event.placeName ?? '';
  const summary = formatEventSummary(event);
  const time = event.timestamp ? new Date(event.timestamp).toLocaleTimeString(undefined, {
    hour12: false, hour: '2-digit', minute: '2-digit', second: '2-digit', fractionalSecondDigits: 3,
  } as Intl.DateTimeFormatOptions) : '';

  div.innerHTML = `
    <div class="flex items-center justify-between">
      <span class="text-gray-400">#${index}</span>
      <span class="text-gray-500">${escapeHtml(time)}</span>
    </div>
    <div class="font-medium text-gray-200 truncate">${escapeHtml(event.type)}${name ? ': ' + escapeHtml(name) : ''}</div>
    <div class="text-gray-400 truncate">${escapeHtml(summary)}</div>
  `;

  return div;
}

function formatEventSummary(event: NetEventInfo): string {
  const d = event.details;
  if (!d) return '';
  switch (event.type) {
    case 'TransitionCompleted':
      return `${d.durationMs ?? 0}ms, ${((d.producedTokens as unknown[]) ?? []).length} tokens produced`;
    case 'TransitionStarted':
      return `${((d.consumedTokens as unknown[]) ?? []).length} tokens consumed`;
    case 'TransitionFailed':
      return `${d.errorMessage ?? 'Unknown error'}`;
    case 'TokenAdded':
    case 'TokenRemoved': {
      const token = d.token as { type?: string; value?: string } | undefined;
      return token ? `${token.type ?? ''}: ${token.value ?? ''}` : '';
    }
    case 'LogMessage':
      return `[${d.level ?? ''}] ${d.message ?? ''}`;
    case 'ExecutionCompleted':
      return `${d.totalDurationMs ?? 0}ms total`;
    default:
      return '';
  }
}

function escapeHtml(str: string): string {
  return str.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

/** Setup scroll listener for follow mode detection. */
export function setupScrollListener(): void {
  const container = el.eventLog;
  let rafPending = false;

  container.addEventListener('scroll', () => {
    if (rafPending) return;
    rafPending = true;
    requestAnimationFrame(() => {
      rafPending = false;
      const atBottom = container.scrollTop + container.clientHeight >= container.scrollHeight - 20;
      shared.virtualLog.followMode = atBottom;
      el.jumpToLatest.classList.toggle('hidden', atBottom);
    });
  });
}
