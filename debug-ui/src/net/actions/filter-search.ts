/**
 * Filter and search transition actions.
 */

import { el } from '../../dom/elements.js';
import type { SearchState } from '../types.js';
import type { NetEventInfo } from '../../protocol/index.js';

/** Compute search matches against the event list. */
export function computeSearchMatches(searchTerm: string, events: readonly NetEventInfo[], totalEvents: number): SearchState {
  if (!searchTerm.trim()) {
    return { searchTerm: '', matches: [], currentMatchIndex: -1 };
  }

  const term = searchTerm.toLowerCase();
  const matches: number[] = [];
  const limit = Math.min(events.length, totalEvents);

  for (let i = 0; i < limit; i++) {
    const event = events[i]!;
    const searchText = [
      String(i),
      event.timestamp ?? '',
      event.type,
      event.transitionName ?? '',
      event.placeName ?? '',
      formatEventForSearch(event),
    ].join(' ').toLowerCase();

    if (searchText.includes(term)) {
      matches.push(i);
    }
  }

  return {
    searchTerm,
    matches,
    currentMatchIndex: matches.length > 0 ? 0 : -1,
  };
}

function formatEventForSearch(event: NetEventInfo): string {
  if (!event.details) return '';
  const parts: string[] = [];
  for (const [key, value] of Object.entries(event.details)) {
    parts.push(`${key}:${String(value)}`);
  }
  return parts.join(' ');
}

/** Update search results UI. */
export function updateSearchUI(searchState: SearchState): void {
  const { matches, currentMatchIndex } = searchState;

  if (matches.length === 0) {
    el.searchResults.textContent = searchState.searchTerm ? '0' : '-';
    el.searchPrev.setAttribute('disabled', '');
    el.searchNext.setAttribute('disabled', '');
  } else {
    el.searchResults.textContent = `${currentMatchIndex + 1}/${matches.length}`;
    el.searchPrev.removeAttribute('disabled');
    el.searchNext.removeAttribute('disabled');
  }

  // Apply search highlighting to visible event entries
  const entries = el.eventLog.querySelectorAll('.event-entry');
  for (const entry of entries) {
    const idx = parseInt((entry as HTMLElement).dataset['eventIndex'] ?? '-1', 10);
    entry.classList.remove('search-match', 'search-current');
    if (matches.includes(idx)) {
      entry.classList.add('search-match');
      if (matches[currentMatchIndex] === idx) {
        entry.classList.add('search-current');
      }
    }
  }
}

/** Navigate to next search match. */
export function nextSearchMatch(current: SearchState): SearchState {
  if (current.matches.length === 0) return current;
  const nextIndex = (current.currentMatchIndex + 1) % current.matches.length;
  return { ...current, currentMatchIndex: nextIndex };
}

/** Navigate to previous search match. */
export function prevSearchMatch(current: SearchState): SearchState {
  if (current.matches.length === 0) return current;
  const prevIndex = (current.currentMatchIndex - 1 + current.matches.length) % current.matches.length;
  return { ...current, currentMatchIndex: prevIndex };
}
