/**
 * All place declarations for the debug UI Petri net.
 */

import { place, environmentPlace } from 'libpetri';
import type { DebugResponse, BreakpointConfig } from '../protocol/index.js';
import type { UIState, SessionData, FilterState, SearchState, ModalContent } from './types.js';

// ======================== Connection Subnet ========================

export const idle = place<void>('idle');
export const connecting = place<void>('connecting');
export const connected = place<void>('connected');
export const waitReconnect = place<void>('waitReconnect');

// ======================== Session Subnet ========================

export const noSession = place<void>('noSession');
export const subscribing = place<string>('subscribing');
export const liveSession = environmentPlace<SessionData>('liveSession');
export const replaySession = environmentPlace<SessionData>('replaySession');

// ======================== State Subnet (resource-place pattern) ========================

export const uiState = place<UIState>('uiState');
export const stateDirty = place<void>('stateDirty');

// ======================== Diagram Subnet ========================

export const dotSource = place<string>('dotSource');
export const svgReady = place<void>('svgReady');
export const highlightDirty = place<void>('highlightDirty');

// ======================== Playback Subnet ========================

export const replayPaused = environmentPlace<void>('replayPaused');
export const replayPlaying = place<void>('replayPlaying');

// ======================== Event Log Subnet ========================

export const logDirty = place<void>('logDirty');
export const filterState = place<FilterState>('filterState');

// ======================== Inspector Subnet ========================

export const markingDirty = place<void>('markingDirty');
export const selectedPlace = place<string>('selectedPlace');
export const tokensDirty = place<void>('tokensDirty');

// ======================== Modal Subnet ========================

export const modalClosed = place<void>('modalClosed');
export const modalOpen = place<ModalContent>('modalOpen');

// ======================== Breakpoint Subnet ========================

export const breakpoints = place<BreakpointConfig[]>('breakpoints');

// ======================== Search Subnet ========================

export const searchState = place<SearchState>('searchState');

// ======================== Environment Places ========================

export const wsOpenSignal = environmentPlace<void>('wsOpenSignal');
export const wsCloseSignal = environmentPlace<void>('wsCloseSignal');
export const wsMessage = environmentPlace<DebugResponse>('wsMessage');

export const userSelectSession = environmentPlace<{ sessionId: string; mode: string }>('userSelectSession');
export const userClickPause = environmentPlace<void>('userClickPause');
export const userClickPlay = environmentPlace<void>('userClickPlay');
export const userClickStepFwd = environmentPlace<void>('userClickStepFwd');
export const userClickStepBack = environmentPlace<void>('userClickStepBack');
export const userClickRestart = environmentPlace<void>('userClickRestart');
export const userClickRunToEnd = environmentPlace<void>('userClickRunToEnd');
export const userSeekSlider = environmentPlace<number>('userSeekSlider');
export const userSetSpeed = environmentPlace<number>('userSetSpeed');
export const userClickPlace = environmentPlace<string>('userClickPlace');
export const userSetBreakpoint = environmentPlace<BreakpointConfig>('userSetBreakpoint');
export const userClearBreakpoint = environmentPlace<string>('userClearBreakpoint');
export const userApplyFilter = environmentPlace<FilterState>('userApplyFilter');
export const userSearch = environmentPlace<string>('userSearch');
export const userSearchPrev = environmentPlace<void>('userSearchPrev');
export const userSearchNext = environmentPlace<void>('userSearchNext');
export const userOpenModal = environmentPlace<ModalContent>('userOpenModal');
export const userCloseModal = environmentPlace<void>('userCloseModal');
export const rafTick = environmentPlace<void>('rafTick');

/** All environment places for executor registration. */
export const allEnvironmentPlaces = new Set([
  wsOpenSignal, wsCloseSignal, wsMessage,
  userSelectSession, userClickPause, userClickPlay,
  userClickStepFwd, userClickStepBack, userClickRestart,
  userClickRunToEnd, userSeekSlider, userSetSpeed,
  userClickPlace, userSetBreakpoint, userClearBreakpoint,
  userApplyFilter, userSearch, userSearchPrev, userSearchNext, userOpenModal, userCloseModal,
  rafTick,
  liveSession, replaySession, replayPaused,
]);
