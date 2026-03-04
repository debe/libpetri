/**
 * Session transition actions: subscribe/unsubscribe, session init.
 */

import { sendCommand } from '../shared-state.js';
import { el } from '../../dom/elements.js';
import type { DebugResponse, SessionSummary, NetStructure } from '../../protocol/index.js';
import type { SessionData, UIState, StructureLookup } from '../types.js';

/** Send listSessions command. */
export function refreshSessions(): void {
  sendCommand({ type: 'listSessions' });
}

/** Populate session dropdown from session list response. */
export function populateSessionList(sessions: readonly SessionSummary[]): void {
  const select = el.sessionSelect;
  const currentValue = select.value;
  select.innerHTML = '<option value="">Select a session...</option>';

  for (const session of sessions) {
    const option = document.createElement('option');
    option.value = session.sessionId;
    const status = session.active ? '(live)' : '(ended)';
    const time = new Date(session.startTime).toLocaleTimeString();
    option.textContent = `${session.netName} ${status} - ${time} (${session.eventCount} events)`;
    select.appendChild(option);
  }

  if (currentValue && select.querySelector(`option[value="${currentValue}"]`)) {
    select.value = currentValue;
  }
}

/** Send subscribe command. */
export function subscribeToSession(sessionId: string, mode: string): void {
  sendCommand({
    type: 'subscribe',
    sessionId,
    mode: mode as 'live' | 'replay',
    fromIndex: 0,
  });
}

/** Send unsubscribe command. */
export function unsubscribeFromSession(sessionId: string): void {
  sendCommand({ type: 'unsubscribe', sessionId });
}

/** Build SessionData from a subscribed response. */
export function buildSessionData(response: Extract<DebugResponse, { type: 'subscribed' }>): SessionData {
  const byGraphId: Record<string, StructureLookup> = {};

  if (response.structure) {
    for (const p of response.structure.places) {
      byGraphId[p.graphId] = {
        name: p.name,
        isTransition: false,
        tokenType: p.tokenType,
        isStart: p.isStart,
        isEnd: p.isEnd,
      };
    }
    for (const t of response.structure.transitions) {
      byGraphId[t.graphId] = {
        name: t.name,
        isTransition: true,
      };
    }
  }

  return {
    sessionId: response.sessionId,
    netName: response.netName,
    dotDiagram: response.dotDiagram,
    structure: response.structure ?? { places: [], transitions: [] },
    mode: response.mode as 'live' | 'replay',
    byGraphId,
  };
}

/** Build initial UIState from subscribed response. */
export function buildInitialUIState(response: Extract<DebugResponse, { type: 'subscribed' }>, isReplay: boolean): UIState {
  if (isReplay) {
    return {
      marking: {},
      enabledTransitions: [],
      inFlightTransitions: [],
      events: [],
      eventIndex: 0,
      totalEvents: response.eventCount,
    };
  }
  return {
    marking: response.currentMarking ?? {},
    enabledTransitions: response.enabledTransitions ?? [],
    inFlightTransitions: response.inFlightTransitions ?? [],
    events: [],
    eventIndex: 0,
    totalEvents: response.eventCount,
  };
}

/** Enable or disable playback controls. */
export function enableControls(enabled: boolean): void {
  const buttons = [
    el.btnRestart, el.btnStepBack, el.btnPause,
    el.btnStepForward, el.btnRunToEnd, el.timelineSlider,
  ];
  for (const btn of buttons) {
    if (enabled) btn.removeAttribute('disabled');
    else btn.setAttribute('disabled', '');
  }
}

/** Update autocomplete datalists from net structure. */
export function updateAutocompleteOptions(structure: NetStructure): void {
  const transitionDatalist = document.getElementById('transition-options')!;
  const placeDatalist = document.getElementById('place-options')!;

  transitionDatalist.innerHTML = '';
  placeDatalist.innerHTML = '';

  for (const t of structure.transitions) {
    const opt = document.createElement('option');
    opt.value = t.name;
    transitionDatalist.appendChild(opt);
  }

  for (const p of structure.places) {
    const opt = document.createElement('option');
    opt.value = p.name;
    placeDatalist.appendChild(opt);
  }
}
