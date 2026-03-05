/**
 * Archive browser actions: list, import, upload, render.
 */

import { sendCommand } from '../shared-state.js';
import { el } from '../../dom/elements.js';
import type { ArchiveSummary } from '../../protocol/index.js';

/** Send listArchives command to server. */
export function requestArchiveList(limit?: number, prefix?: string): void {
  sendCommand({ type: 'listArchives', limit, prefix });
}

/** Send importArchive command to server. */
export function requestImportArchive(sessionId: string): void {
  sendCommand({ type: 'importArchive', sessionId });
}

/** Render archive list into the modal table. */
export function renderArchiveList(archives: readonly ArchiveSummary[]): void {
  const table = el.archiveTable;
  if (archives.length === 0) {
    table.innerHTML = '<div class="text-gray-500 text-center py-4">No archives found</div>';
    return;
  }

  table.innerHTML = '';
  for (const archive of archives) {
    const row = document.createElement('div');
    row.className = 'flex items-center justify-between px-3 py-2 bg-gray-700 rounded hover:bg-gray-600';

    const sizeKb = (archive.sizeBytes / 1024).toFixed(1);
    const date = new Date(archive.lastModified).toLocaleString();

    row.innerHTML = `
      <div class="flex-1 min-w-0">
        <div class="text-gray-200 truncate font-mono text-xs">${escapeHtml(archive.sessionId)}</div>
        <div class="text-gray-500 text-xs">${sizeKb} KB &middot; ${date}</div>
      </div>
      <button class="ml-3 px-3 py-1 bg-blue-600 rounded text-xs hover:bg-blue-700 shrink-0"
              data-archive-import="${escapeHtml(archive.sessionId)}">Import</button>
    `;
    table.appendChild(row);
  }
}

/** Upload a file as a base64-encoded archive. */
export function uploadArchiveFile(file: File): void {
  el.archiveStatus.textContent = `Uploading ${file.name}...`;
  const reader = new FileReader();
  reader.onload = () => {
    const arrayBuffer = reader.result as ArrayBuffer;
    const bytes = new Uint8Array(arrayBuffer);
    // Convert to base64
    let binary = '';
    for (let i = 0; i < bytes.length; i++) {
      binary += String.fromCharCode(bytes[i]!);
    }
    const base64 = btoa(binary);
    sendCommand({ type: 'uploadArchive', fileName: file.name, data: base64 });
  };
  reader.onerror = () => {
    el.archiveStatus.textContent = `Failed to read file: ${file.name}`;
  };
  reader.readAsArrayBuffer(file);
}

/** Show the archive browser modal. */
export function showArchiveBrowser(storageAvailable: boolean): void {
  el.archiveModal.classList.remove('hidden');
  // Show/hide the storage-dependent sections
  if (!storageAvailable) {
    el.archiveStatus.textContent = 'No archive storage configured — upload only';
  } else {
    el.archiveStatus.textContent = '';
  }
}

/** Hide the archive browser modal. */
export function hideArchiveBrowser(): void {
  el.archiveModal.classList.add('hidden');
}

function escapeHtml(str: string): string {
  return str.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}
