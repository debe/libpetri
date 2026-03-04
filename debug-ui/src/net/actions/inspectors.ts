/**
 * Inspector transition actions: marking panel, token list rendering.
 */

import { el } from '../../dom/elements.js';
import type { UIState, SessionData } from '../types.js';

/** Update the marking inspector panel. */
export function updateMarkingInspector(uiState: UIState, session: SessionData | null): void {
  const container = el.markingInspector;
  const marking = uiState.marking;

  const entries = Object.entries(marking).filter(([, tokens]) => tokens && tokens.length > 0);

  if (entries.length === 0) {
    container.innerHTML = '<div class="text-gray-500">No marking data</div>';
    return;
  }

  // Sort by place name
  entries.sort((a, b) => a[0].localeCompare(b[0]));

  const html = entries.map(([placeName, tokens]) => {
    const count = tokens.length;
    const graphId = session?.structure.places.find(p => p.name === placeName)?.graphId ?? '';
    return `<div class="flex items-center justify-between p-1.5 bg-gray-700 rounded cursor-pointer hover:bg-gray-600" data-place="${escapeAttr(placeName)}" data-graph-id="${escapeAttr(graphId)}">
      <span class="text-gray-200 truncate flex-1">${escapeHtml(placeName)}</span>
      <span class="text-gray-400 ml-2 shrink-0">${count} token${count !== 1 ? 's' : ''}</span>
    </div>`;
  }).join('');

  container.innerHTML = html;
}

/** Render token inspector for a selected place. */
export function renderTokenInspector(placeName: string, uiState: UIState): void {
  const container = el.tokenInspector;
  const tokens = uiState.marking[placeName];

  if (!tokens || tokens.length === 0) {
    container.innerHTML = `<div class="text-gray-400">No tokens in <span class="text-gray-200">${escapeHtml(placeName)}</span></div>`;
    return;
  }

  const html = tokens.map((token, i) => {
    const valuePreview = token.value
      ? (token.value.length > 60 ? token.value.slice(0, 60) + '...' : token.value)
      : 'null';
    const time = token.timestamp ? new Date(token.timestamp).toLocaleTimeString() : '';
    return `<div class="p-2 bg-gray-700 rounded cursor-pointer hover:bg-gray-600" data-token-index="${i}" data-place="${escapeAttr(placeName)}">
      <div class="flex items-center justify-between">
        <span class="text-gray-200">${escapeHtml(token.type)}</span>
        <span class="text-gray-500 text-xs">${escapeHtml(time)}</span>
      </div>
      <div class="text-gray-400 truncate mt-1">${escapeHtml(valuePreview)}</div>
    </div>`;
  }).join('');

  container.innerHTML = `<div class="mb-2 text-gray-200 font-medium">${escapeHtml(placeName)}</div>
    <div class="space-y-1">${html}</div>
    ${tokens.length > 1 ? `<button class="mt-2 text-xs text-blue-400 hover:text-blue-300" data-view-all="${escapeAttr(placeName)}">View All (${tokens.length} tokens)</button>` : ''}`;
}

function escapeHtml(str: string): string {
  return str.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

function escapeAttr(str: string): string {
  return str.replace(/&/g, '&amp;').replace(/"/g, '&quot;').replace(/'/g, '&#39;');
}
