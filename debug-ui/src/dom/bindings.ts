/**
 * Wire DOM events to environment place injections.
 */

import type { BitmapNetExecutor } from 'libpetri';
import { el } from './elements.js';
import * as p from '../net/places.js';
import { shared } from '../net/shared-state.js';
import { CONFIG } from '../net/types.js';
import type { FilterState, ModalContent } from '../net/types.js';
import type { BreakpointConfig, BreakpointType } from '../protocol/index.js';
import { resetZoom } from '../net/actions/diagram.js';
import { refreshSessions } from '../net/actions/session.js';
import { generateBreakpointId, showBreakpointForm, hideBreakpointForm, findBreakpoint } from '../net/actions/breakpoints.js';
import { copyModalJson } from '../net/actions/modal.js';
import { setupScrollListener } from '../net/actions/event-log.js';
import { requestArchiveList, hideArchiveBrowser } from '../net/actions/archive.js';

/** Bind all DOM events to executor environment place injections. */
export function bindDomEvents(executor: BitmapNetExecutor): void {
  // ======================== Header controls ========================

  el.sessionSelect.addEventListener('change', () => {
    const sessionId = el.sessionSelect.value;
    if (sessionId) {
      const mode = el.modeSelect.value;
      executor.injectValue(p.userSelectSession, { sessionId, mode });
      // Update URL for deep-linking
      const url = new URL(window.location.href);
      url.searchParams.set('sessionId', sessionId);
      window.history.replaceState(null, '', url.toString());
    }
  });

  el.refreshSessions.addEventListener('click', () => {
    refreshSessions();
  });

  el.resetZoom.addEventListener('click', () => {
    resetZoom();
  });

  // ======================== Playback controls ========================

  el.btnPause.addEventListener('click', () => {
    // Toggle: if playing → pause, if paused → play
    const isPaused = !el.iconPlay.classList.contains('hidden');
    if (isPaused) {
      executor.injectValue(p.userClickPlay, undefined);
    } else {
      executor.injectValue(p.userClickPause, undefined);
    }
  });

  el.btnStepForward.addEventListener('click', () => {
    executor.injectValue(p.userClickStepFwd, undefined);
  });

  el.btnStepBack.addEventListener('click', () => {
    executor.injectValue(p.userClickStepBack, undefined);
  });

  el.btnRestart.addEventListener('click', () => {
    executor.injectValue(p.userClickRestart, undefined);
  });

  el.btnRunToEnd.addEventListener('click', () => {
    executor.injectValue(p.userClickRunToEnd, undefined);
  });

  // ======================== Timeline slider ========================

  let sliderRafPending = false;
  el.timelineSlider.addEventListener('input', () => {
    if (sliderRafPending) return;
    sliderRafPending = true;
    requestAnimationFrame(() => {
      sliderRafPending = false;
      const slider = el.timelineSlider;
      const value = parseInt(slider.value, 10);
      const max = parseInt(slider.max, 10) || CONFIG.sliderResolution;
      const totalEvents = shared.replay.allEvents.length;
      const targetIndex = Math.round((value / max) * totalEvents);
      executor.injectValue(p.userSeekSlider, targetIndex);
    });
  });

  // ======================== Speed controls ========================

  document.querySelectorAll('.speed-btn').forEach(btn => {
    btn.addEventListener('click', () => {
      const speed = parseFloat((btn as HTMLElement).dataset['speed'] ?? '1');
      executor.injectValue(p.userSetSpeed, speed);
    });
  });

  // ======================== Filter controls ========================

  el.applyFilter.addEventListener('click', () => {
    const filter: FilterState = {
      eventTypes: el.filterEventType.value ? [el.filterEventType.value] : [],
      transitionNames: el.filterTransition.value ? [el.filterTransition.value] : [],
      placeNames: el.filterPlace.value ? [el.filterPlace.value] : [],
      filteredIndices: null,
    };
    executor.injectValue(p.userApplyFilter, filter);
  });

  el.clearFilter.addEventListener('click', () => {
    el.filterEventType.value = '';
    el.filterTransition.value = '';
    el.filterPlace.value = '';
    const filter: FilterState = {
      eventTypes: [],
      transitionNames: [],
      placeNames: [],
      filteredIndices: null,
    };
    executor.injectValue(p.userApplyFilter, filter);
  });

  // ======================== Search controls ========================

  let searchDebounce: ReturnType<typeof setTimeout> | null = null;
  el.searchInput.addEventListener('input', () => {
    if (searchDebounce) clearTimeout(searchDebounce);
    searchDebounce = setTimeout(() => {
      executor.injectValue(p.userSearch, el.searchInput.value);
    }, 200);
  });

  el.searchPrev.addEventListener('click', () => {
    executor.injectValue(p.userSearchPrev, undefined);
  });

  el.searchNext.addEventListener('click', () => {
    executor.injectValue(p.userSearchNext, undefined);
  });

  el.searchClear.addEventListener('click', () => {
    el.searchInput.value = '';
    executor.injectValue(p.userSearch, '');
  });

  // ======================== Breakpoint controls ========================

  el.addBreakpoint.addEventListener('click', () => {
    showBreakpointForm();
  });

  el.bpSave.addEventListener('click', () => {
    const bp: BreakpointConfig = {
      id: generateBreakpointId(),
      type: el.bpType.value as BreakpointType,
      target: el.bpTarget.value || null,
      enabled: true,
    };
    executor.injectValue(p.userSetBreakpoint, bp);
    hideBreakpointForm();
    el.bpTarget.value = '';
  });

  el.bpCancel.addEventListener('click', () => {
    hideBreakpointForm();
  });

  // Breakpoint list delegation: toggle and delete
  el.breakpointList.addEventListener('click', (e) => {
    const target = e.target as HTMLElement;
    if (target.classList.contains('bp-delete')) {
      const bpId = target.dataset['bpId'];
      if (bpId) executor.injectValue(p.userClearBreakpoint, bpId);
    }
  });

  el.breakpointList.addEventListener('change', (e) => {
    const target = e.target as HTMLInputElement;
    if (target.classList.contains('bp-toggle')) {
      const bpId = target.dataset['bpId'];
      if (!bpId) return;
      const bp = findBreakpoint(bpId);
      if (bp) {
        executor.injectValue(p.userSetBreakpoint, { ...bp, enabled: !bp.enabled });
      }
    }
  });

  // ======================== Event log interactions ========================

  el.eventLog.addEventListener('click', (e) => {
    const entry = (e.target as HTMLElement).closest('.event-entry') as HTMLElement | null;
    if (!entry) return;
    const idx = parseInt(entry.dataset['eventIndex'] ?? '-1', 10);
    if (idx < 0) return;

    // Open modal with event details
    const content: ModalContent = {
      title: `Event #${idx}`,
      subtitle: '',
      json: JSON.stringify(entry.dataset, null, 2),
    };
    executor.injectValue(p.userOpenModal, content);
  });

  el.jumpToLatest.addEventListener('click', () => {
    const container = el.eventLog;
    container.scrollTop = container.scrollHeight;
    shared.virtualLog.followMode = true;
    el.jumpToLatest.classList.add('hidden');
  });

  // ======================== Marking inspector click → place inspection ========================

  el.markingInspector.addEventListener('click', (e) => {
    const entry = (e.target as HTMLElement).closest('[data-place]') as HTMLElement | null;
    if (!entry) return;
    const placeName = entry.dataset['place'];
    if (placeName) {
      executor.injectValue(p.userClickPlace, placeName);
    }
  });

  // ======================== Token inspector click → value modal ========================

  el.tokenInspector.addEventListener('click', (e) => {
    const entry = (e.target as HTMLElement).closest('[data-token-index]') as HTMLElement | null;
    if (!entry) return;
    const indexStr = entry.dataset['tokenIndex'];
    const placeName = entry.dataset['place'];
    if (indexStr == null || !placeName) return;

    const tokens = (() => {
      const m = executor.getMarking().peekTokens(p.uiState);
      if (m.length === 0) return null;
      const state = m[0]!.value as import('../net/types.js').UIState;
      return state.marking[placeName];
    })();
    if (!tokens) return;

    const index = parseInt(indexStr, 10);
    const token = tokens[index];
    if (!token) return;

    const content: ModalContent = {
      title: placeName,
      subtitle: `Token ${index + 1} of ${tokens.length} · ${token.type}`,
      json: token.value ?? 'null',
    };
    executor.injectValue(p.userOpenModal, content);
  });

  // ======================== Diagram click → place/transition inspection ========================

  el.dotDiagram.addEventListener('click', (e) => {
    if (!shared.svgNodeCache) return;
    const target = e.target as Element;
    const nodeGroup = target.closest('g.node');
    if (!nodeGroup) return;

    const title = nodeGroup.querySelector('title');
    if (!title) return;
    const graphId = title.textContent?.trim() ?? '';

    // Only inspect places (p_ prefix)
    if (graphId.startsWith('p_')) {
      // Find place name from structure
      // We need access to session data - simplified: use graphId lookup
      executor.injectValue(p.userClickPlace, graphId);
    }
  });

  // Context menu on diagram
  el.dotDiagram.addEventListener('contextmenu', (e) => {
    e.preventDefault();
    if (!shared.svgNodeCache) return;
    const target = e.target as Element;
    const nodeGroup = target.closest('g.node');
    if (!nodeGroup) return;

    const title = nodeGroup.querySelector('title');
    if (!title) return;
    const graphId = title.textContent?.trim() ?? '';

    showContextMenu(e as MouseEvent, graphId, executor);
  });

  // Close context menu on click elsewhere
  document.addEventListener('click', () => {
    el.diagramContextMenu.classList.add('hidden');
  });

  // ======================== Modal controls ========================

  el.modalClose.addEventListener('click', () => {
    executor.injectValue(p.userCloseModal, undefined);
  });

  el.modalCopy.addEventListener('click', () => {
    copyModalJson();
  });

  el.valueModal.addEventListener('click', (e) => {
    if (e.target === el.valueModal) {
      executor.injectValue(p.userCloseModal, undefined);
    }
  });

  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape') {
      executor.injectValue(p.userCloseModal, undefined);
    }
  });

  // ======================== Net-name filter ========================

  el.netNameFilter.addEventListener('change', () => {
    executor.injectValue(p.userFilterNetName, el.netNameFilter.value);
  });

  // ======================== Archive browser ========================

  el.archiveBtn.addEventListener('click', () => {
    executor.injectValue(p.userOpenArchiveBrowser, undefined);
  });

  el.archiveCloseBtn.addEventListener('click', () => {
    hideArchiveBrowser();
  });

  el.archiveModal.addEventListener('click', (e) => {
    if (e.target === el.archiveModal) {
      hideArchiveBrowser();
    }
  });

  // Delegated click on import buttons
  el.archiveTable.addEventListener('click', (e) => {
    const target = (e.target as HTMLElement).closest('[data-archive-import]') as HTMLElement | null;
    if (target) {
      const sessionId = target.dataset['archiveImport'];
      if (sessionId) {
        executor.injectValue(p.userImportArchive, sessionId);
      }
    }
  });

  // File upload via input
  el.archiveUpload.addEventListener('change', () => {
    const file = el.archiveUpload.files?.[0];
    if (file) {
      executor.injectValue(p.userUploadArchive, file);
      el.archiveUpload.value = '';
    }
  });

  // Drop zone click → trigger file input
  el.archiveDropZone.addEventListener('click', () => {
    el.archiveUpload.click();
  });

  // Drag-and-drop handlers
  el.archiveDropZone.addEventListener('dragover', (e) => {
    e.preventDefault();
    el.archiveDropZone.classList.add('border-blue-500');
  });

  el.archiveDropZone.addEventListener('dragleave', () => {
    el.archiveDropZone.classList.remove('border-blue-500');
  });

  el.archiveDropZone.addEventListener('drop', (e) => {
    e.preventDefault();
    el.archiveDropZone.classList.remove('border-blue-500');
    const file = e.dataTransfer?.files[0];
    if (file) {
      executor.injectValue(p.userUploadArchive, file);
    }
  });

  // Archive search with debounce
  let archiveSearchDebounce: ReturnType<typeof setTimeout> | null = null;
  el.archiveSearch.addEventListener('input', () => {
    if (archiveSearchDebounce) clearTimeout(archiveSearchDebounce);
    archiveSearchDebounce = setTimeout(() => {
      requestArchiveList(50, el.archiveSearch.value || undefined);
    }, 300);
  });

  // Escape closes archive modal too
  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape' && !el.archiveModal.classList.contains('hidden')) {
      hideArchiveBrowser();
    }
  });

  // ======================== Virtual scroll setup ========================

  setupScrollListener();
}

function showContextMenu(e: MouseEvent, graphId: string, executor: BitmapNetExecutor): void {
  const menu = el.diagramContextMenu;
  menu.classList.remove('hidden');
  menu.style.left = `${e.clientX}px`;
  menu.style.top = `${e.clientY}px`;

  el.ctxMenuHeader.textContent = graphId;

  const isPlace = graphId.startsWith('p_');

  el.ctxBpPlaceOptions.classList.toggle('hidden', !isPlace);
  el.ctxBpTransitionOptions.classList.toggle('hidden', isPlace);

  // Wire context menu breakpoint options
  const options = menu.querySelectorAll('.ctx-bp-option');
  for (const opt of options) {
    const clone = opt.cloneNode(true) as HTMLElement;
    opt.replaceWith(clone);
    clone.addEventListener('click', () => {
      const bpType = clone.dataset['bpType'] as BreakpointType;
      const bp: BreakpointConfig = {
        id: generateBreakpointId(),
        type: bpType,
        target: graphId, // Note: should resolve to actual name
        enabled: true,
      };
      executor.injectValue(p.userSetBreakpoint, bp);
      menu.classList.add('hidden');
    });
  }

  // Inspect button
  el.ctxMenuInspect.onclick = () => {
    if (isPlace) {
      executor.injectValue(p.userClickPlace, graphId);
    }
    menu.classList.add('hidden');
  };
}
