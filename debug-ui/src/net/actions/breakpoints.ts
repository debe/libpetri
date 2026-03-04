/**
 * Breakpoint transition actions: list rendering, context menu.
 */

import { el } from '../../dom/elements.js';
import type { BreakpointConfig } from '../../protocol/index.js';

/** Last rendered breakpoint list, for toggle lookups. */
let lastBreakpoints: readonly BreakpointConfig[] = [];

/** Find a breakpoint by ID from the last rendered list. */
export function findBreakpoint(id: string): BreakpointConfig | undefined {
  return lastBreakpoints.find(bp => bp.id === id);
}

/** Render the breakpoint list. */
export function renderBreakpointList(breakpointList: readonly BreakpointConfig[]): void {
  lastBreakpoints = breakpointList;
  const container = el.breakpointList;

  if (breakpointList.length === 0) {
    container.innerHTML = '<div class="text-gray-500">No breakpoints</div>';
    return;
  }

  const html = breakpointList.map(bp => {
    const typeLabel = formatBreakpointType(bp.type);
    const target = bp.target ?? '(any)';
    const enabledClass = bp.enabled ? 'text-gray-200' : 'text-gray-500 line-through';
    return `<div class="flex items-center gap-2 p-1.5 bg-gray-700 rounded" data-bp-id="${escapeAttr(bp.id)}">
      <input type="checkbox" ${bp.enabled ? 'checked' : ''} class="bp-toggle shrink-0" data-bp-id="${escapeAttr(bp.id)}">
      <div class="flex-1 min-w-0">
        <div class="${enabledClass} text-xs truncate">${escapeHtml(typeLabel)}: ${escapeHtml(target)}</div>
      </div>
      <button class="bp-delete text-gray-500 hover:text-red-400 shrink-0" data-bp-id="${escapeAttr(bp.id)}">&times;</button>
    </div>`;
  }).join('');

  container.innerHTML = html;
}

function formatBreakpointType(type: string): string {
  const map: Record<string, string> = {
    TRANSITION_ENABLED: 'Transition Enabled',
    TRANSITION_START: 'Transition Start',
    TRANSITION_COMPLETE: 'Transition Complete',
    TRANSITION_FAIL: 'Transition Fail',
    TOKEN_ADDED: 'Token Added',
    TOKEN_REMOVED: 'Token Removed',
  };
  return map[type] ?? type;
}

/** Generate a unique breakpoint ID. */
export function generateBreakpointId(): string {
  return `bp-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
}

/** Show the breakpoint form. */
export function showBreakpointForm(): void {
  el.breakpointForm.classList.remove('hidden');
}

/** Hide the breakpoint form. */
export function hideBreakpointForm(): void {
  el.breakpointForm.classList.add('hidden');
}

/** Highlight a breakpoint in the list when hit. */
export function highlightBreakpointInList(bpId: string): void {
  const container = el.breakpointList;
  const bpEl = container.querySelector(`[data-bp-id="${bpId}"]`);
  if (bpEl) {
    bpEl.classList.add('ring-1', 'ring-yellow-500');
    setTimeout(() => bpEl.classList.remove('ring-1', 'ring-yellow-500'), 3000);
  }
}

function escapeHtml(str: string): string {
  return str.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

function escapeAttr(str: string): string {
  return str.replace(/&/g, '&amp;').replace(/"/g, '&quot;');
}
