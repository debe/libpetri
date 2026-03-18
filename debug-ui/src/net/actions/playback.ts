/**
 * Playback transition actions: checkpoint building, seeking, replay scheduling.
 */

import { shared } from '../shared-state.js';
import { el } from '../../dom/elements.js';
import type { UIState, Checkpoint } from '../types.js';
import { CONFIG } from '../types.js';
import type { NetEventInfo, BreakpointConfig } from '../../protocol/index.js';

/** Apply a single event to UIState, returning an updated copy. */
export function applyEventToState(state: UIState, event: NetEventInfo): UIState {
  const marking = { ...state.marking };
  let enabled = [...state.enabledTransitions];
  let inFlight = [...state.inFlightTransitions];

  switch (event.type) {
    case 'TokenAdded': {
      const place = event.placeName!;
      const token = event.details?.token;
      if (token) {
        marking[place] = [...(marking[place] ?? []), token as UIState['marking'][string][number]];
      }
      break;
    }
    case 'TokenRemoved': {
      const place = event.placeName!;
      const tokens = marking[place];
      if (tokens && tokens.length > 0) {
        marking[place] = tokens.slice(1);
      }
      break;
    }
    case 'MarkingSnapshot': {
      const newMarking = (event.details?.marking ?? {}) as Record<string, readonly UIState['marking'][string][number][]>;
      Object.keys(marking).forEach(k => delete marking[k]);
      Object.assign(marking, newMarking);
      break;
    }
    case 'TransitionEnabled':
      if (event.transitionName && !enabled.includes(event.transitionName)) {
        enabled = [...enabled, event.transitionName];
      }
      break;
    case 'TransitionStarted':
      if (event.transitionName) {
        enabled = enabled.filter(t => t !== event.transitionName);
        if (!inFlight.includes(event.transitionName)) {
          inFlight = [...inFlight, event.transitionName];
        }
      }
      break;
    case 'TransitionCompleted':
    case 'TransitionFailed':
    case 'TransitionTimedOut':
    case 'ActionTimedOut':
      if (event.transitionName) {
        inFlight = inFlight.filter(t => t !== event.transitionName);
      }
      break;
  }

  return { ...state, marking, enabledTransitions: enabled, inFlightTransitions: inFlight };
}

/** Build checkpoints from replay events for efficient seeking. */
export function buildCheckpoints(events: readonly NetEventInfo[], fromIndex: number): Checkpoint[] {
  const checkpoints = [...shared.replay.checkpoints];
  const interval = shared.replay.checkpointInterval;

  const tempMarking: Record<string, unknown[]> = {};
  const tempEnabled: string[] = [];
  const tempInFlight: string[] = [];
  let startIndex = 0;

  if (fromIndex > 0 && checkpoints.length > 0) {
    const lastCp = checkpoints[checkpoints.length - 1]!;
    Object.assign(tempMarking, structuredClone(lastCp.marking));
    tempEnabled.push(...lastCp.enabledTransitions);
    tempInFlight.push(...lastCp.inFlightTransitions);
    startIndex = lastCp.index;
  }

  for (let i = startIndex; i < events.length; i++) {
    const event = events[i]!;
    applyEventToTemp(tempMarking, tempEnabled, tempInFlight, event);

    if ((i + 1) % interval === 0) {
      checkpoints.push({
        index: i + 1,
        marking: structuredClone(tempMarking) as Checkpoint['marking'],
        enabledTransitions: [...tempEnabled],
        inFlightTransitions: [...tempInFlight],
      });
    }
  }

  return checkpoints;
}

function applyEventToTemp(
  marking: Record<string, unknown[]>,
  enabled: string[],
  inFlight: string[],
  event: NetEventInfo,
): void {
  switch (event.type) {
    case 'TokenAdded':
      if (event.placeName) {
        if (!marking[event.placeName]) marking[event.placeName] = [];
        marking[event.placeName]!.push(event.details?.token);
      }
      break;
    case 'TokenRemoved':
      if (event.placeName && marking[event.placeName]?.length) {
        marking[event.placeName]!.shift();
      }
      break;
    case 'TransitionEnabled':
      if (event.transitionName && !enabled.includes(event.transitionName)) enabled.push(event.transitionName);
      break;
    case 'TransitionStarted': {
      if (event.transitionName) {
        const idx = enabled.indexOf(event.transitionName);
        if (idx >= 0) enabled.splice(idx, 1);
        if (!inFlight.includes(event.transitionName)) inFlight.push(event.transitionName);
      }
      break;
    }
    case 'TransitionCompleted':
    case 'TransitionFailed':
    case 'TransitionTimedOut':
    case 'ActionTimedOut': {
      if (event.transitionName) {
        const idx = inFlight.indexOf(event.transitionName);
        if (idx >= 0) inFlight.splice(idx, 1);
      }
      break;
    }
    case 'MarkingSnapshot': {
      Object.keys(marking).forEach(k => delete marking[k]);
      Object.assign(marking, (event.details?.marking ?? {}));
      break;
    }
  }
}

/** Seek to a specific event index using checkpoints. */
export function seekToIndex(targetIndex: number): UIState {
  const checkpoints = shared.replay.checkpoints;
  const events = shared.replay.allEvents;

  stopPlayback();

  let startIndex = 0;
  let marking: Record<string, readonly unknown[]> = {};
  let enabled: readonly string[] = [];
  let inFlight: readonly string[] = [];

  // Find nearest checkpoint <= targetIndex
  for (let i = checkpoints.length - 1; i >= 0; i--) {
    const cp = checkpoints[i]!;
    if (cp.index <= targetIndex) {
      startIndex = cp.index;
      marking = structuredClone(cp.marking);
      enabled = [...cp.enabledTransitions];
      inFlight = [...cp.inFlightTransitions];
      break;
    }
  }

  // Replay from checkpoint to target
  let state: UIState = {
    marking: marking as UIState['marking'],
    enabledTransitions: [...enabled],
    inFlightTransitions: [...inFlight],
    events: events,
    eventIndex: targetIndex,
    totalEvents: events.length,
  };

  for (let i = startIndex; i < targetIndex && i < events.length; i++) {
    const applied = applyEventToState(state, events[i]!);
    state = { ...applied, events: events, eventIndex: targetIndex, totalEvents: events.length };
  }

  return state;
}

/** Stop playback timer. */
export function stopPlayback(): void {
  if (shared.playback.timer) {
    clearTimeout(shared.playback.timer);
    shared.playback.timer = null;
  }
  if (shared.playback.animationFrame) {
    cancelAnimationFrame(shared.playback.animationFrame);
    shared.playback.animationFrame = null;
  }
}

/** Update playback controls based on paused state. */
export function updatePlaybackControls(paused: boolean | 'breakpoint'): void {
  const iconPause = el.iconPause;
  const iconPlay = el.iconPlay;
  const btn = el.btnPause;

  if (paused) {
    iconPause.classList.add('hidden');
    iconPlay.classList.remove('hidden');
  } else {
    iconPause.classList.remove('hidden');
    iconPlay.classList.add('hidden');
  }

  btn.classList.remove('bg-green-700', 'hover:bg-green-600', 'bg-yellow-600', 'hover:bg-yellow-500');
  if (paused === 'breakpoint') {
    btn.classList.add('bg-yellow-600', 'hover:bg-yellow-500');
  } else {
    btn.classList.add('bg-green-700', 'hover:bg-green-600');
  }
}

/** Update timeline position text and slider. */
export function updateTimelinePosition(eventIndex: number, totalEvents: number): void {
  el.timelinePosition.textContent = `${eventIndex} / ${totalEvents}`;
  const slider = el.timelineSlider;
  if (totalEvents > 0) {
    (slider as HTMLInputElement).value = String(Math.round((eventIndex / totalEvents) * CONFIG.sliderResolution));
    (slider as HTMLInputElement).max = String(CONFIG.sliderResolution);
  } else {
    (slider as HTMLInputElement).value = '0';
  }
}

/** Check if event matches any breakpoint. Returns matching BP or null. */
export function checkClientBreakpoints(event: NetEventInfo, breakpointList: readonly BreakpointConfig[]): BreakpointConfig | null {
  for (const bp of breakpointList) {
    if (!bp.enabled) continue;
    if (matchesBreakpoint(bp, event)) return bp;
  }
  return null;
}

function matchesBreakpoint(bp: BreakpointConfig, event: NetEventInfo): boolean {
  const typeMap: Record<string, string> = {
    TRANSITION_ENABLED: 'TransitionEnabled',
    TRANSITION_START: 'TransitionStarted',
    TRANSITION_COMPLETE: 'TransitionCompleted',
    TRANSITION_FAIL: 'TransitionFailed',
    TOKEN_ADDED: 'TokenAdded',
    TOKEN_REMOVED: 'TokenRemoved',
  };

  const expectedType = typeMap[bp.type];
  if (event.type !== expectedType) return false;

  if (bp.target === null) return true;

  const targetName = event.transitionName ?? event.placeName;
  return targetName === bp.target;
}

/** Calculate playback delay in ms from speed multiplier. */
export function calculatePlaybackDelay(speed: number): number {
  const baseDelay = 50;
  const raw = baseDelay / speed;
  return Math.max(CONFIG.minPlaybackDelay, Math.min(CONFIG.maxPlaybackDelay, raw));
}

/** Update speed button highlighting. */
export function updateSpeedButtons(speed: number): void {
  document.querySelectorAll('.speed-btn').forEach(btn => {
    const btnSpeed = parseFloat((btn as HTMLElement).dataset['speed'] ?? '1');
    if (btnSpeed === speed) {
      btn.className = 'speed-btn px-2 py-1 bg-blue-600 rounded text-xs';
    } else {
      btn.className = 'speed-btn px-2 py-1 bg-gray-700 rounded text-xs hover:bg-gray-600 transition-colors';
    }
  });
}
