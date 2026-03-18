/**
 * Cached DOM element references (typed).
 */

function getEl<T extends HTMLElement>(id: string): T {
  const element = document.getElementById(id);
  if (!element) throw new Error(`Element not found: #${id}`);
  return element as T;
}

/** Lazily initialized cached element references. */
export let el: {
  statusDot: HTMLElement;
  statusText: HTMLElement;
  sessionSelect: HTMLSelectElement;
  refreshSessions: HTMLButtonElement;
  resetZoom: HTMLButtonElement;
  diagramContainer: HTMLElement;
  dotDiagram: HTMLElement;
  noSession: HTMLElement;
  markingInspector: HTMLElement;
  tokenInspector: HTMLElement;
  breakpointList: HTMLElement;
  addBreakpoint: HTMLButtonElement;
  breakpointForm: HTMLElement;
  bpType: HTMLSelectElement;
  bpTarget: HTMLInputElement;
  bpSave: HTMLButtonElement;
  bpCancel: HTMLButtonElement;
  eventLog: HTMLElement;
  eventCount: HTMLElement;
  clearEvents: HTMLElement;
  jumpToLatest: HTMLButtonElement;
  filterEventType: HTMLSelectElement;
  filterTransition: HTMLInputElement;
  filterPlace: HTMLInputElement;
  filterExcludeTransition: HTMLInputElement;
  filterExcludePlace: HTMLInputElement;
  applyFilter: HTMLButtonElement;
  clearFilter: HTMLButtonElement;
  searchInput: HTMLInputElement;
  searchResults: HTMLElement;
  searchPrev: HTMLButtonElement;
  searchNext: HTMLButtonElement;
  searchClear: HTMLButtonElement;
  btnRestart: HTMLButtonElement;
  btnStepBack: HTMLButtonElement;
  btnPause: HTMLButtonElement;
  iconPause: HTMLElement;
  iconPlay: HTMLElement;
  btnStepForward: HTMLButtonElement;
  btnRunToEnd: HTMLButtonElement;
  timelineSlider: HTMLInputElement;
  timelinePosition: HTMLElement;
  modeSelect: HTMLSelectElement;
  diagramContextMenu: HTMLElement;
  ctxMenuHeader: HTMLElement;
  ctxMenuInspect: HTMLElement;
  ctxBpPlaceOptions: HTMLElement;
  ctxBpTransitionOptions: HTMLElement;
  valueModal: HTMLElement;
  modalTitle: HTMLElement;
  modalSubtitle: HTMLElement;
  modalCopy: HTMLButtonElement;
  modalClose: HTMLButtonElement;
  modalJson: HTMLElement;
  netNameFilter: HTMLSelectElement;
  archiveBtn: HTMLButtonElement;
  archiveModal: HTMLElement;
  archiveSearch: HTMLInputElement;
  archiveTable: HTMLElement;
  archiveUpload: HTMLInputElement;
  archiveDropZone: HTMLElement;
  archiveCloseBtn: HTMLButtonElement;
  archiveStatus: HTMLElement;
};

/** Initialize all cached element references. Must be called after DOMContentLoaded. */
export function initElements(): void {
  el = {
    statusDot: getEl('status-dot'),
    statusText: getEl('status-text'),
    sessionSelect: getEl<HTMLSelectElement>('session-select'),
    refreshSessions: getEl<HTMLButtonElement>('refresh-sessions'),
    resetZoom: getEl<HTMLButtonElement>('reset-zoom'),
    diagramContainer: getEl('diagram-container'),
    dotDiagram: getEl('dot-diagram'),
    noSession: getEl('no-session'),
    markingInspector: getEl('marking-inspector'),
    tokenInspector: getEl('token-inspector'),
    breakpointList: getEl('breakpoint-list'),
    addBreakpoint: getEl<HTMLButtonElement>('add-breakpoint'),
    breakpointForm: getEl('breakpoint-form'),
    bpType: getEl<HTMLSelectElement>('bp-type'),
    bpTarget: getEl<HTMLInputElement>('bp-target'),
    bpSave: getEl<HTMLButtonElement>('bp-save'),
    bpCancel: getEl<HTMLButtonElement>('bp-cancel'),
    eventLog: getEl('event-log'),
    eventCount: getEl('event-count'),
    clearEvents: getEl('clear-events'),
    jumpToLatest: getEl<HTMLButtonElement>('jump-to-latest'),
    filterEventType: getEl<HTMLSelectElement>('filter-event-type'),
    filterTransition: getEl<HTMLInputElement>('filter-transition'),
    filterPlace: getEl<HTMLInputElement>('filter-place'),
    filterExcludeTransition: getEl<HTMLInputElement>('filter-exclude-transition'),
    filterExcludePlace: getEl<HTMLInputElement>('filter-exclude-place'),
    applyFilter: getEl<HTMLButtonElement>('apply-filter'),
    clearFilter: getEl<HTMLButtonElement>('clear-filter'),
    searchInput: getEl<HTMLInputElement>('search-input'),
    searchResults: getEl('search-results'),
    searchPrev: getEl<HTMLButtonElement>('search-prev'),
    searchNext: getEl<HTMLButtonElement>('search-next'),
    searchClear: getEl<HTMLButtonElement>('search-clear'),
    btnRestart: getEl<HTMLButtonElement>('btn-restart'),
    btnStepBack: getEl<HTMLButtonElement>('btn-step-back'),
    btnPause: getEl<HTMLButtonElement>('btn-pause'),
    iconPause: getEl('icon-pause'),
    iconPlay: getEl('icon-play'),
    btnStepForward: getEl<HTMLButtonElement>('btn-step-forward'),
    btnRunToEnd: getEl<HTMLButtonElement>('btn-run-to-end'),
    timelineSlider: getEl<HTMLInputElement>('timeline-slider'),
    timelinePosition: getEl('timeline-position'),
    modeSelect: getEl<HTMLSelectElement>('mode-select'),
    diagramContextMenu: getEl('diagram-context-menu'),
    ctxMenuHeader: getEl('ctx-menu-header'),
    ctxMenuInspect: getEl('ctx-menu-inspect'),
    ctxBpPlaceOptions: getEl('ctx-bp-place-options'),
    ctxBpTransitionOptions: getEl('ctx-bp-transition-options'),
    valueModal: getEl('value-modal'),
    modalTitle: getEl('modal-title'),
    modalSubtitle: getEl('modal-subtitle'),
    modalCopy: getEl<HTMLButtonElement>('modal-copy'),
    modalClose: getEl<HTMLButtonElement>('modal-close'),
    modalJson: getEl('modal-json'),
    netNameFilter: getEl<HTMLSelectElement>('net-name-filter'),
    archiveBtn: getEl<HTMLButtonElement>('archive-btn'),
    archiveModal: getEl('archive-modal'),
    archiveSearch: getEl<HTMLInputElement>('archive-search'),
    archiveTable: getEl('archive-table'),
    archiveUpload: getEl<HTMLInputElement>('archive-upload'),
    archiveDropZone: getEl('archive-drop-zone'),
    archiveCloseBtn: getEl<HTMLButtonElement>('archive-close'),
    archiveStatus: getEl('archive-status'),
  };
}
