/**
 * Modal transition actions: show/close, JSON syntax highlighting, copy.
 */

import { el } from '../../dom/elements.js';
import type { ModalContent } from '../types.js';

/** Show the value modal with content. */
export function showModal(content: ModalContent): void {
  el.modalTitle.textContent = content.title;
  el.modalSubtitle.textContent = content.subtitle;
  el.modalJson.innerHTML = syntaxHighlightJson(content.json);
  el.valueModal.classList.remove('hidden');
}

/** Close the value modal. */
export function closeModal(): void {
  el.valueModal.classList.add('hidden');
}

/** Copy modal JSON to clipboard. */
export function copyModalJson(): void {
  const text = el.modalJson.textContent ?? '';
  navigator.clipboard.writeText(text).then(() => {
    const btn = el.modalCopy;
    const orig = btn.textContent;
    btn.textContent = 'Copied!';
    btn.classList.replace('bg-blue-600', 'bg-green-600');
    setTimeout(() => {
      btn.textContent = orig;
      btn.classList.replace('bg-green-600', 'bg-blue-600');
    }, 1500);
  });
}

/** Escape HTML entities to prevent XSS when inserting into innerHTML. */
function escapeHtml(s: string): string {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

/** Syntax highlight JSON string for display. */
function syntaxHighlightJson(json: string): string {
  try {
    const parsed = JSON.parse(json);
    json = JSON.stringify(parsed, null, 2);
  } catch {
    // If not valid JSON, display as-is
  }

  return escapeHtml(json).replace(
    /("(?:[^"\\]|\\.)*")\s*:/g,
    '<span class="json-key">$1</span>:'
  ).replace(
    /:\s*("(?:[^"\\]|\\.)*")/g,
    ': <span class="json-string">$1</span>'
  ).replace(
    /:\s*(-?\d+\.?\d*(?:[eE][+-]?\d+)?)/g,
    ': <span class="json-number">$1</span>'
  ).replace(
    /:\s*(true|false)/g,
    ': <span class="json-boolean">$1</span>'
  ).replace(
    /:\s*(null)/g,
    ': <span class="json-null">$1</span>'
  );
}
