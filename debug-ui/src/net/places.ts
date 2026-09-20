/**
 * All place declarations for the debug UI Petri net.
 */

import { place, environmentPlace, type Place } from 'libpetri';
import type { DebugResponse, BreakpointConfig } from '../protocol/index.js';
import type { UIState, SessionData, FilterState, SearchState, ModalContent, DeadLetter } from './types.js';

// ======================== Connection Subnet ========================

export const idle = place<void>('idle');
export const connecting = place<void>('connecting');
export const connected = place<void>('connected');
export const waitReconnect = place<void>('waitReconnect');

// ======================== Session Subnet ========================

export const noSession = place<void>('noSession');
export const subscribing = place<string>('subscribing');
export const subscribedSession = place<string>('subscribedSession');
// The mode of the subscribed session. `t_on_subscribed` emits exactly one of them with
// `subscribedSession`, and the transition that leaves the session takes it back:
//
//   noSession + subscribing + subscribedSession = 1
//   subscribedSession = liveSession + replaySession            (P-invariants, proven in tests/)
export const liveSession = place<SessionData>('liveSession');
export const replaySession = place<SessionData>('replaySession');

// ======================== State Subnet (resource-place pattern) ========================

export const uiState = place<UIState>('uiState');
export const stateDirty = place<void>('stateDirty');

// ======================== Diagram Subnet ========================

export const dotSource = place<string>('dotSource');
export const svgReady = place<void>('svgReady');
export const highlightDirty = place<void>('highlightDirty');

// ======================== Playback Subnet ========================

// The mode of a replay session: replaySession = replayPaused + replayPlaying + breakpointPaused.
export const replayPaused = place<void>('replayPaused');
export const replayPlaying = place<void>('replayPlaying');
export const breakpointPaused = place<void>('breakpointPaused');
/**
 * The playback clock. `t_replay_play` emits the first tick; each later one is injected by the
 * timer the step before it armed. A tick that arrives while nothing is playing is consumed by
 * `t_drop_stale_tick`, so none rests here to double the rate of the next play.
 */
export const autoStepTick = environmentPlace<void>('autoStepTick');

// ======================== Repaint Subnet ========================
//
// `t_frame` turns the animation-frame ticks into one frame token per panel. A panel that is
// dirty repaints on its token, a panel that is not lets it go: a frame token never rests.

export const frameHighlight = place<void>('frameHighlight');
export const frameLog = place<void>('frameLog');
export const frameMarking = place<void>('frameMarking');

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

// ======================== Message Router Subnet ========================
//
// One typed place per protocol message. `t_route_message` (definition.ts) moves each
// `wsMessage` onto exactly one of them, or onto `deadLetter`; the handler that consumes it
// hands `routerReady` back. The permit makes the router strictly FIFO across types:
//
//   routerReady + Σ msg* + deadLetter = 1      (a P-invariant, proven in tests/)

/** A response of one protocol type. */
export type ResponseOf<K extends DebugResponse['type']> = Extract<DebugResponse, { type: K }>;

/** The router's permit: present while no message is between `wsMessage` and its handler. */
export const routerReady = place<void>('routerReady');

export const msgSessionList = place<ResponseOf<'sessionList'>>('msgSessionList');
export const msgSubscribed = place<ResponseOf<'subscribed'>>('msgSubscribed');
export const msgUnsubscribed = place<ResponseOf<'unsubscribed'>>('msgUnsubscribed');
export const msgEvent = place<ResponseOf<'event'>>('msgEvent');
export const msgEventBatch = place<ResponseOf<'eventBatch'>>('msgEventBatch');
export const msgMarkingSnapshot = place<ResponseOf<'markingSnapshot'>>('msgMarkingSnapshot');
export const msgPlaybackState = place<ResponseOf<'playbackStateChanged'>>('msgPlaybackState');
export const msgFilterApplied = place<ResponseOf<'filterApplied'>>('msgFilterApplied');
export const msgBreakpointHit = place<ResponseOf<'breakpointHit'>>('msgBreakpointHit');
export const msgBreakpointList = place<ResponseOf<'breakpointList'>>('msgBreakpointList');
export const msgBreakpointSet = place<ResponseOf<'breakpointSet'>>('msgBreakpointSet');
export const msgBreakpointCleared = place<ResponseOf<'breakpointCleared'>>('msgBreakpointCleared');
export const msgError = place<ResponseOf<'error'>>('msgError');
export const msgArchiveList = place<ResponseOf<'archiveList'>>('msgArchiveList');
export const msgArchiveImported = place<ResponseOf<'archiveImported'>>('msgArchiveImported');

/**
 * The route of every protocol message type. The mapped type makes it exhaustive: a response
 * added to the protocol without a route here does not compile.
 */
export const messageRoutes: { readonly [K in DebugResponse['type']]: Place<ResponseOf<K>> } = {
  sessionList: msgSessionList,
  subscribed: msgSubscribed,
  unsubscribed: msgUnsubscribed,
  event: msgEvent,
  eventBatch: msgEventBatch,
  markingSnapshot: msgMarkingSnapshot,
  playbackStateChanged: msgPlaybackState,
  filterApplied: msgFilterApplied,
  breakpointHit: msgBreakpointHit,
  breakpointList: msgBreakpointList,
  breakpointSet: msgBreakpointSet,
  breakpointCleared: msgBreakpointCleared,
  error: msgError,
  archiveList: msgArchiveList,
  archiveImported: msgArchiveImported,
};

/**
 * Messages no handler took: an unknown or malformed frame, a message that arrived in a session
 * state with no use for it, or one whose handler threw. `t_log_dead_letter` logs each and hands
 * the permit back, so nothing rests here.
 */
export const deadLetter = place<DeadLetter>('deadLetter');

// ======================== Environment Places ========================

export const wsOpenSignal = environmentPlace<void>('wsOpenSignal');
export const wsCloseSignal = environmentPlace<void>('wsCloseSignal');
export const wsMessage = environmentPlace<DebugResponse>('wsMessage');

/** The `?sessionId=` of the page URL, injected once at startup: the session to select when the first list arrives. */
export const deepLink = environmentPlace<string>('deepLink');
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
export const userOpenArchiveBrowser = environmentPlace<void>('userOpenArchiveBrowser');
export const userImportArchive = environmentPlace<string>('userImportArchive');
export const userUploadArchive = environmentPlace<File>('userUploadArchive');
export const userFilterNetName = environmentPlace<string>('userFilterNetName');
export const userToggleSubnets = environmentPlace<void>('userToggleSubnets');
export const rafTick = environmentPlace<void>('rafTick');

/** All environment places for executor registration. */
export const allEnvironmentPlaces = new Set([
  wsOpenSignal, wsCloseSignal, wsMessage,
  userSelectSession, userClickPause, userClickPlay,
  userClickStepFwd, userClickStepBack, userClickRestart,
  userClickRunToEnd, userSeekSlider, userSetSpeed,
  userClickPlace, userSetBreakpoint, userClearBreakpoint,
  userApplyFilter, userSearch, userSearchPrev, userSearchNext, userOpenModal, userCloseModal,
  userOpenArchiveBrowser, userImportArchive, userUploadArchive, userFilterNetName,
  userToggleSubnets,
  rafTick, deepLink, autoStepTick,
]);
