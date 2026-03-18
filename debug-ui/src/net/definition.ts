/**
 * Debug UI Petri net definition.
 *
 * Builds the CTPN whose execution IS the debug UI behavior.
 * Environment places receive DOM events and WebSocket messages.
 * Transition actions perform DOM updates and WebSocket I/O.
 */

import {
  PetriNet, Transition, tokenOf,
  one, outPlace, and,
  immediate, delayed,
  type BitmapNetExecutor, type Place, type Token,
} from 'libpetri';
import * as p from './places.js';
import type { UIState, SessionData, FilterState, SearchState, ModalContent } from './types.js';
import type { DebugResponse, BreakpointConfig } from '../protocol/index.js';
import { shared, sendCommand } from './shared-state.js';
import { createWebSocket, setConnected, setDisconnected, setConnecting } from './actions/connection.js';
import {
  refreshSessions, populateSessionList, subscribeToSession, unsubscribeFromSession,
  buildSessionData, buildInitialUIState,
  enableControls, updateAutocompleteOptions,
} from './actions/session.js';
import {
  requestArchiveList, renderArchiveList, showArchiveBrowser, hideArchiveBrowser,
  requestImportArchive, uploadArchiveFile,
} from './actions/archive.js';
import { renderDotDiagram, updateDiagramHighlighting } from './actions/diagram.js';
import { renderVisibleEvents } from './actions/event-log.js';
import {
  applyEventToState, buildCheckpoints, seekToIndex,
  stopPlayback, updatePlaybackControls, updateTimelinePosition,
  updateSpeedButtons, calculatePlaybackDelay, checkClientBreakpoints,
} from './actions/playback.js';
import { updateMarkingInspector, renderTokenInspector } from './actions/inspectors.js';
import { showModal, closeModal } from './actions/modal.js';
import {
  renderBreakpointList, highlightBreakpointInList,
} from './actions/breakpoints.js';
import { computeSearchMatches, updateSearchUI, nextSearchMatch, prevSearchMatch } from './actions/filter-search.js';

/** Reference to the executor, set after creation. */
let executor: BitmapNetExecutor;

export function setExecutor(exec: BitmapNetExecutor): void {
  executor = exec;
}

/**
 * Builds the debug UI PetriNet.
 *
 * Initial tokens: idle(1), noSession(1), uiState(1), filterState(1),
 * modalClosed(1), breakpoints(1), searchState(1)
 *
 * @petrinet ./definition#buildDebugNet()
 */
export function buildDebugNet(): {
  net: PetriNet;
  initialTokens: Map<Place<unknown>, Token<unknown>[]>;
} {
  // ======================== Connection transitions ========================

  const t_connect = Transition.builder('t_connect')
    .inputs(one(p.idle))
    .outputs(outPlace(p.connecting))
    .timing(immediate())
    .action(async (ctx) => {
      setConnecting();
      createWebSocket(executor);
      ctx.output(p.connecting, undefined);
    })
    .build();

  const t_on_open = Transition.builder('t_on_open')
    .inputs(one(p.connecting), one(p.wsOpenSignal.place))
    .outputs(outPlace(p.connected))
    .timing(immediate())
    .action(async (ctx) => {
      setConnected();
      refreshSessions();
      ctx.output(p.connected, undefined);
    })
    .build();

  const t_on_close_connecting = Transition.builder('t_on_close_connecting')
    .inputs(one(p.connecting), one(p.wsCloseSignal.place))
    .outputs(outPlace(p.waitReconnect))
    .timing(immediate())
    .action(async (ctx) => {
      setDisconnected();
      ctx.output(p.waitReconnect, undefined);
    })
    .build();

  const t_on_close_connected = Transition.builder('t_on_close_connected')
    .inputs(one(p.connected), one(p.wsCloseSignal.place))
    .outputs(outPlace(p.waitReconnect))
    .timing(immediate())
    .action(async (ctx) => {
      setDisconnected();
      ctx.output(p.waitReconnect, undefined);
    })
    .build();

  const t_reconnect = Transition.builder('t_reconnect')
    .inputs(one(p.waitReconnect))
    .outputs(outPlace(p.idle))
    .timing(delayed(2000))
    .action(async (ctx) => {
      ctx.output(p.idle, undefined);
    })
    .build();

  // ======================== Session transitions ========================

  const t_subscribe = Transition.builder('t_subscribe')
    .inputs(one(p.noSession), one(p.userSelectSession.place))
    .reads(p.connected)
    .outputs(outPlace(p.subscribing))
    .timing(immediate())
    .action(async (ctx) => {
      const selection = ctx.input(p.userSelectSession.place) as { sessionId: string; mode: string };
      subscribeToSession(selection.sessionId, selection.mode);
      ctx.output(p.subscribing, selection.sessionId);
    })
    .build();

  const t_unsubscribe_and_switch = Transition.builder('t_unsubscribe_and_switch')
    .inputs(one(p.subscribedSession), one(p.userSelectSession.place), one(p.uiState))
    .reads(p.connected)
    .outputs(outPlace(p.subscribing))
    .timing(immediate())
    .action(async (ctx) => {
      const oldSessionId = ctx.input(p.subscribedSession) as string;
      const selection = ctx.input(p.userSelectSession.place) as { sessionId: string; mode: string };
      unsubscribeFromSession(oldSessionId);
      shared.currentSession = null;
      shared.currentMode = null;
      shared.replay = { allEvents: [], checkpoints: [], checkpointInterval: 20 };
      subscribeToSession(selection.sessionId, selection.mode);
      ctx.output(p.subscribing, selection.sessionId);
    })
    .build();

  const t_on_subscribed = Transition.builder('t_on_subscribed')
    .inputs(one(p.subscribing), one(p.wsMessage.place, (msg: DebugResponse) => msg.type === 'subscribed'))
    .outputs(and(outPlace(p.uiState), outPlace(p.dotSource), outPlace(p.stateDirty), outPlace(p.subscribedSession)))
    .timing(immediate())
    .action(async (ctx) => {
      const msg = ctx.input(p.wsMessage.place) as Extract<DebugResponse, { type: 'subscribed' }>;
      const sessionData = buildSessionData(msg);
      const isReplay = sessionData.mode === 'replay';
      const initialState = buildInitialUIState(msg, isReplay);

      if (isReplay) {
        shared.replay = { allEvents: [], checkpoints: [], checkpointInterval: 20 };
      }

      shared.currentSession = sessionData;
      shared.currentMode = isReplay ? 'replay' : 'live';

      enableControls(true);
      updateAutocompleteOptions(sessionData.structure);
      updatePlaybackControls(isReplay);
      updateTimelinePosition(initialState.eventIndex, initialState.totalEvents);

      // Store session in the appropriate place via executor injection
      if (isReplay) {
        executor.injectValue(p.replaySession, sessionData);
        executor.injectValue(p.replayPaused, undefined);
      } else {
        executor.injectValue(p.liveSession, sessionData);
      }

      ctx.output(p.uiState, initialState);
      ctx.output(p.dotSource, msg.dotDiagram);
      ctx.output(p.stateDirty, undefined);
      ctx.output(p.subscribedSession, msg.sessionId);
    })
    .build();

  // ======================== Message dispatch transitions ========================

  const t_on_session_list = Transition.builder('t_on_session_list')
    .inputs(one(p.wsMessage.place, (msg: DebugResponse) => msg.type === 'sessionList'))
    .timing(immediate())
    .action(async (ctx) => {
      const msg = ctx.input(p.wsMessage.place) as Extract<DebugResponse, { type: 'sessionList' }>;
      shared.allSessions = [...msg.sessions];
      populateSessionList(msg.sessions, shared.netNameFilter || undefined);

      // Handle deep-link: auto-select session from URL param
      if (shared.pendingDeepLink) {
        const target = shared.pendingDeepLink;
        shared.pendingDeepLink = null;
        const found = msg.sessions.find(s => s.sessionId === target);
        if (found) {
          executor.injectValue(p.userSelectSession, { sessionId: target, mode: 'replay' });
        }
      }
    })
    .build();

  const t_on_event = Transition.builder('t_on_event')
    .inputs(one(p.uiState), one(p.wsMessage.place, (msg: DebugResponse) => msg.type === 'event'))
    .outputs(and(outPlace(p.uiState), outPlace(p.stateDirty)))
    .timing(immediate())
    .action(async (ctx) => {
      const msg = ctx.input(p.wsMessage.place) as Extract<DebugResponse, { type: 'event' }>;
      const state = ctx.input(p.uiState) as UIState;
      const updated = applyEventToState(state, msg.event);
      const newState: UIState = {
        ...updated,
        events: [...state.events, msg.event],
        eventIndex: msg.index + 1,
        totalEvents: Math.max(state.totalEvents, msg.index + 1),
      };
      updateTimelinePosition(newState.eventIndex, newState.totalEvents);
      ctx.output(p.uiState, newState);
      ctx.output(p.stateDirty, undefined);
    })
    .build();

  const t_on_event_batch = Transition.builder('t_on_event_batch')
    .inputs(one(p.uiState), one(p.wsMessage.place, (msg: DebugResponse) => msg.type === 'eventBatch'))
    .outputs(and(outPlace(p.uiState), outPlace(p.stateDirty)))
    .timing(immediate())
    .action(async (ctx) => {
      const msg = ctx.input(p.wsMessage.place) as Extract<DebugResponse, { type: 'eventBatch' }>;
      let state = ctx.input(p.uiState) as UIState;

      const isReplay = shared.currentMode === 'replay';

      if (isReplay) {
        const prevLength = shared.replay.allEvents.length;
        shared.replay.allEvents.push(...msg.events);
        shared.replay.checkpoints = buildCheckpoints(shared.replay.allEvents, prevLength);
        state = {
          ...state,
          events: shared.replay.allEvents,
          totalEvents: shared.replay.allEvents.length,
        };
      } else {
        const newEvents = [...state.events, ...msg.events];
        let updated = state;
        for (const event of msg.events) {
          updated = applyEventToState(updated, event);
        }
        state = {
          ...updated,
          events: newEvents,
          eventIndex: msg.startIndex + msg.events.length,
          totalEvents: Math.max(state.totalEvents, msg.startIndex + msg.events.length),
        };
      }

      updateTimelinePosition(state.eventIndex, state.totalEvents);
      ctx.output(p.uiState, state);
      ctx.output(p.stateDirty, undefined);
    })
    .build();

  const t_on_marking_snapshot = Transition.builder('t_on_marking_snapshot')
    .inputs(one(p.uiState), one(p.wsMessage.place, (msg: DebugResponse) => msg.type === 'markingSnapshot'))
    .outputs(and(outPlace(p.uiState), outPlace(p.stateDirty)))
    .timing(immediate())
    .action(async (ctx) => {
      const msg = ctx.input(p.wsMessage.place) as Extract<DebugResponse, { type: 'markingSnapshot' }>;
      const state = ctx.input(p.uiState) as UIState;
      ctx.output(p.uiState, {
        ...state,
        marking: msg.marking ?? {},
        enabledTransitions: msg.enabledTransitions ?? [],
        inFlightTransitions: msg.inFlightTransitions ?? [],
      });
      ctx.output(p.stateDirty, undefined);
    })
    .build();

  const t_on_playback_state = Transition.builder('t_on_playback_state')
    .inputs(one(p.wsMessage.place, (msg: DebugResponse) => msg.type === 'playbackStateChanged'))
    .timing(immediate())
    .action(async (ctx) => {
      const msg = ctx.input(p.wsMessage.place) as Extract<DebugResponse, { type: 'playbackStateChanged' }>;
      updatePlaybackControls(msg.paused);
      shared.playback.speed = msg.speed;
      updateSpeedButtons(msg.speed);
    })
    .build();

  const t_on_breakpoint_hit = Transition.builder('t_on_breakpoint_hit')
    .inputs(one(p.wsMessage.place, (msg: DebugResponse) => msg.type === 'breakpointHit'))
    .timing(immediate())
    .action(async (ctx) => {
      const msg = ctx.input(p.wsMessage.place) as Extract<DebugResponse, { type: 'breakpointHit' }>;
      updatePlaybackControls('breakpoint');
      highlightBreakpointInList(msg.breakpointId);
    })
    .build();

  const t_on_bp_list = Transition.builder('t_on_bp_list')
    .inputs(one(p.breakpoints), one(p.wsMessage.place, (msg: DebugResponse) => msg.type === 'breakpointList'))
    .outputs(outPlace(p.breakpoints))
    .timing(immediate())
    .action(async (ctx) => {
      const msg = ctx.input(p.wsMessage.place) as Extract<DebugResponse, { type: 'breakpointList' }>;
      renderBreakpointList(msg.breakpoints);
      ctx.output(p.breakpoints, [...msg.breakpoints]);
    })
    .build();

  const t_on_bp_set = Transition.builder('t_on_bp_set')
    .inputs(one(p.wsMessage.place, (msg: DebugResponse) => msg.type === 'breakpointSet'))
    .timing(immediate())
    .action(async (_ctx) => {
      // Confirmation received, no action needed (UI already updated optimistically)
    })
    .build();

  const t_on_bp_cleared = Transition.builder('t_on_bp_cleared')
    .inputs(one(p.wsMessage.place, (msg: DebugResponse) => msg.type === 'breakpointCleared'))
    .timing(immediate())
    .action(async (_ctx) => {
      // Confirmation received
    })
    .build();

  const t_on_filter_applied = Transition.builder('t_on_filter_applied')
    .inputs(one(p.wsMessage.place, (msg: DebugResponse) => msg.type === 'filterApplied'))
    .timing(immediate())
    .action(async (_ctx) => {
      // Confirmation received
    })
    .build();

  const t_on_unsubscribed = Transition.builder('t_on_unsubscribed')
    .inputs(one(p.wsMessage.place, (msg: DebugResponse) => msg.type === 'unsubscribed'))
    .timing(immediate())
    .action(async (_ctx) => {
      // Cleanup handled by switch session transition
    })
    .build();

  const t_on_error = Transition.builder('t_on_error')
    .inputs(one(p.wsMessage.place, (msg: DebugResponse) => msg.type === 'error'))
    .timing(immediate())
    .action(async (ctx) => {
      const msg = ctx.input(p.wsMessage.place) as Extract<DebugResponse, { type: 'error' }>;
      console.error(`Debug protocol error [${msg.code}]: ${msg.message}`);
    })
    .build();

  // ======================== Diagram transitions ========================

  const t_render_dot = Transition.builder('t_render_dot')
    .inputs(one(p.dotSource))
    .outputs(outPlace(p.svgReady))
    .timing(immediate())
    .action(async (ctx) => {
      const dot = ctx.input(p.dotSource) as string;
      await renderDotDiagram(dot);
      ctx.output(p.svgReady, undefined);
    })
    .build();

  // ======================== UI update fan-out ========================

  const t_fan_out_dirty = Transition.builder('t_fan_out_dirty')
    .inputs(one(p.stateDirty))
    .outputs(and(outPlace(p.highlightDirty), outPlace(p.logDirty), outPlace(p.markingDirty)))
    .timing(immediate())
    .action(async (ctx) => {
      ctx.output(p.highlightDirty, undefined);
      ctx.output(p.logDirty, undefined);
      ctx.output(p.markingDirty, undefined);
    })
    .build();

  const t_update_highlighting = Transition.builder('t_update_highlighting')
    .inputs(one(p.highlightDirty), one(p.rafTick.place))
    .reads(p.svgReady, p.uiState)
    .timing(immediate())
    .action(async (ctx) => {
      const state = ctx.read(p.uiState) as UIState;
      const session = shared.currentSession;
      updateDiagramHighlighting(state, session);
    })
    .build();

  const t_update_event_log = Transition.builder('t_update_event_log')
    .inputs(one(p.logDirty), one(p.rafTick.place))
    .reads(p.uiState, p.filterState)
    .timing(immediate())
    .action(async (ctx) => {
      const state = ctx.read(p.uiState) as UIState;
      const filter = ctx.read(p.filterState) as FilterState;
      renderVisibleEvents(state, filter);
    })
    .build();

  const t_update_marking = Transition.builder('t_update_marking')
    .inputs(one(p.markingDirty), one(p.rafTick.place))
    .reads(p.uiState)
    .timing(immediate())
    .action(async (ctx) => {
      const state = ctx.read(p.uiState) as UIState;
      const session = shared.currentSession;
      updateMarkingInspector(state, session);
    })
    .build();

  // ======================== Replay playback transitions ========================

  const t_replay_play = Transition.builder('t_replay_play')
    .inputs(one(p.replayPaused.place), one(p.userClickPlay.place))
    .reads(p.replaySession.place)
    .outputs(outPlace(p.replayPlaying))
    .timing(immediate())
    .action(async (ctx) => {
      updatePlaybackControls(false);
      // Kickstart auto-playback loop via environment place injection
      executor.injectValue(p.autoStepTick, undefined);
      ctx.output(p.replayPlaying, undefined);
    })
    .build();

  const t_replay_auto_step = Transition.builder('t_replay_auto_step')
    .inputs(one(p.autoStepTick.place))
    .reads(p.replayPlaying)
    .timing(immediate())
    .action(async () => {
      // Check if at end of replay
      const state = executor.getMarking().peekTokens(p.uiState);
      const currentState = state.length > 0 ? state[0]!.value as UIState : null;
      const events = shared.replay.allEvents;

      if (!currentState || currentState.eventIndex >= events.length) {
        // At end — stop playback and switch back to paused
        stopPlayback();
        updatePlaybackControls(true);
        executor.injectValue(p.userClickPause, undefined);
        return;
      }

      // Check breakpoints before stepping (skip if we just resumed from this index)
      if (shared.playback.breakpointHitIndex !== currentState.eventIndex) {
        const nextEvent = events[currentState.eventIndex]!;
        const bpTokens = executor.getMarking().peekTokens(p.breakpoints);
        const bpList = bpTokens.length > 0 ? bpTokens[0]!.value as BreakpointConfig[] : [];
        const hit = checkClientBreakpoints(nextEvent, bpList);
        if (hit) {
          shared.playback.breakpointHitIndex = currentState.eventIndex;
          stopPlayback();
          highlightBreakpointInList(hit.id);
          executor.injectValue(p.breakpointHit, undefined);
          return;
        }
      }
      // Clear breakpointHitIndex — we're advancing past it
      shared.playback.breakpointHitIndex = null;

      // Step forward by injecting userClickStepFwd
      executor.injectValue(p.userClickStepFwd, undefined);

      // Schedule next tick with speed-adjusted delay
      const delay = calculatePlaybackDelay(shared.playback.speed);
      shared.playback.timer = setTimeout(() => {
        executor.injectValue(p.autoStepTick, undefined);
      }, delay);
    })
    .build();

  const t_replay_pause = Transition.builder('t_replay_pause')
    .inputs(one(p.replayPlaying), one(p.userClickPause.place))
    .outputs(outPlace(p.replayPaused.place))
    .timing(immediate())
    .action(async (ctx) => {
      stopPlayback();
      updatePlaybackControls(true);
      ctx.output(p.replayPaused.place, undefined);
    })
    .build();

  const t_replay_breakpoint_stop = Transition.builder('t_replay_breakpoint_stop')
    .inputs(one(p.replayPlaying), one(p.breakpointHit.place))
    .outputs(outPlace(p.breakpointPaused))
    .timing(immediate())
    .action(async (ctx) => {
      stopPlayback();
      updatePlaybackControls('breakpoint');
      ctx.output(p.breakpointPaused, undefined);
    })
    .build();

  const t_replay_play_from_bp = Transition.builder('t_replay_play_from_bp')
    .inputs(one(p.breakpointPaused), one(p.userClickPlay.place))
    .reads(p.replaySession.place)
    .outputs(outPlace(p.replayPlaying))
    .timing(immediate())
    .action(async (ctx) => {
      updatePlaybackControls(false);
      executor.injectValue(p.autoStepTick, undefined);
      ctx.output(p.replayPlaying, undefined);
    })
    .build();

  const t_replay_step_fwd = Transition.builder('t_replay_step_fwd')
    .inputs(one(p.uiState), one(p.userClickStepFwd.place))
    .reads(p.replaySession.place)
    .outputs(and(outPlace(p.uiState), outPlace(p.stateDirty)))
    .timing(immediate())
    .action(async (ctx) => {
      const state = ctx.input(p.uiState) as UIState;
      const events = shared.replay.allEvents;
      if (state.eventIndex < events.length) {
        const event = events[state.eventIndex]!;
        const updated = applyEventToState(state, event);
        const newState: UIState = {
          ...updated,
          eventIndex: state.eventIndex + 1,
          totalEvents: events.length,
        };
        updateTimelinePosition(newState.eventIndex, newState.totalEvents);
        ctx.output(p.uiState, newState);
      } else {
        ctx.output(p.uiState, state);
      }
      ctx.output(p.stateDirty, undefined);
    })
    .build();

  const t_replay_step_back = Transition.builder('t_replay_step_back')
    .inputs(one(p.uiState), one(p.userClickStepBack.place))
    .reads(p.replaySession.place)
    .outputs(and(outPlace(p.uiState), outPlace(p.stateDirty)))
    .timing(immediate())
    .action(async (ctx) => {
      shared.playback.breakpointHitIndex = null;
      const state = ctx.input(p.uiState) as UIState;
      if (state.eventIndex > 0) {
        const newState = seekToIndex(state.eventIndex - 1);
        updateTimelinePosition(newState.eventIndex, newState.totalEvents);
        ctx.output(p.uiState, newState);
      } else {
        ctx.output(p.uiState, state);
      }
      ctx.output(p.stateDirty, undefined);
    })
    .build();

  const t_replay_seek = Transition.builder('t_replay_seek')
    .inputs(one(p.uiState), one(p.userSeekSlider.place))
    .reads(p.replaySession.place)
    .outputs(and(outPlace(p.uiState), outPlace(p.stateDirty)))
    .timing(immediate())
    .action(async (ctx) => {
      shared.playback.breakpointHitIndex = null;
      const targetIndex = ctx.input(p.userSeekSlider.place) as number;
      const newState = seekToIndex(targetIndex);
      updateTimelinePosition(newState.eventIndex, newState.totalEvents);
      ctx.output(p.uiState, newState);
      ctx.output(p.stateDirty, undefined);
    })
    .build();

  const t_replay_restart = Transition.builder('t_replay_restart')
    .inputs(one(p.uiState), one(p.userClickRestart.place))
    .reads(p.replaySession.place)
    .outputs(and(outPlace(p.uiState), outPlace(p.stateDirty)))
    .timing(immediate())
    .action(async (ctx) => {
      shared.playback.breakpointHitIndex = null;
      const newState = seekToIndex(0);
      updateTimelinePosition(0, newState.totalEvents);
      ctx.output(p.uiState, newState);
      ctx.output(p.stateDirty, undefined);
    })
    .build();

  const t_replay_run_to_end = Transition.builder('t_replay_run_to_end')
    .inputs(one(p.uiState), one(p.userClickRunToEnd.place))
    .reads(p.replaySession.place)
    .outputs(and(outPlace(p.uiState), outPlace(p.stateDirty)))
    .timing(immediate())
    .action(async (ctx) => {
      shared.playback.breakpointHitIndex = null;
      const events = shared.replay.allEvents;
      const newState = seekToIndex(events.length);
      updateTimelinePosition(newState.eventIndex, newState.totalEvents);
      ctx.output(p.uiState, newState);
      ctx.output(p.stateDirty, undefined);
    })
    .build();

  // ======================== Live mode control transitions ========================

  const t_live_pause = Transition.builder('t_live_pause')
    .inputs(one(p.userClickPause.place))
    .reads(p.liveSession.place)
    .timing(immediate())
    .action(async (ctx) => {
      const session = ctx.read(p.liveSession.place) as SessionData;
      sendCommand({ type: 'pause', sessionId: session.sessionId });
    })
    .build();

  const t_live_resume = Transition.builder('t_live_resume')
    .inputs(one(p.userClickPlay.place))
    .reads(p.liveSession.place)
    .timing(immediate())
    .action(async (ctx) => {
      const session = ctx.read(p.liveSession.place) as SessionData;
      sendCommand({ type: 'resume', sessionId: session.sessionId });
    })
    .build();

  const t_live_step_fwd = Transition.builder('t_live_step_fwd')
    .inputs(one(p.userClickStepFwd.place))
    .reads(p.liveSession.place)
    .timing(immediate())
    .action(async (ctx) => {
      const session = ctx.read(p.liveSession.place) as SessionData;
      sendCommand({ type: 'stepForward', sessionId: session.sessionId });
    })
    .build();

  const t_live_step_back = Transition.builder('t_live_step_back')
    .inputs(one(p.userClickStepBack.place))
    .reads(p.liveSession.place)
    .timing(immediate())
    .action(async (ctx) => {
      const session = ctx.read(p.liveSession.place) as SessionData;
      sendCommand({ type: 'stepBackward', sessionId: session.sessionId });
    })
    .build();

  // ======================== Inspector transitions ========================

  const t_inspect_place = Transition.builder('t_inspect_place')
    .inputs(one(p.userClickPlace.place))
    .reads(p.uiState)
    .outputs(outPlace(p.selectedPlace))
    .timing(immediate())
    .action(async (ctx) => {
      const raw = ctx.input(p.userClickPlace.place) as string;
      // Resolve graphId (e.g. "p_start") to place name (e.g. "start") if needed
      const lookup = shared.currentSession?.byGraphId[raw];
      const placeName = lookup && !lookup.isTransition ? lookup.name : raw;
      const state = ctx.read(p.uiState) as UIState;
      renderTokenInspector(placeName, state);
      ctx.output(p.selectedPlace, placeName);
    })
    .build();

  // ======================== Modal transitions ========================

  const t_open_modal = Transition.builder('t_open_modal')
    .inputs(one(p.modalClosed), one(p.userOpenModal.place))
    .outputs(outPlace(p.modalOpen))
    .timing(immediate())
    .action(async (ctx) => {
      const content = ctx.input(p.userOpenModal.place) as ModalContent;
      showModal(content);
      ctx.output(p.modalOpen, content);
    })
    .build();

  const t_close_modal = Transition.builder('t_close_modal')
    .inputs(one(p.modalOpen), one(p.userCloseModal.place))
    .outputs(outPlace(p.modalClosed))
    .timing(immediate())
    .action(async (ctx) => {
      closeModal();
      ctx.output(p.modalClosed, undefined);
    })
    .build();

  // ======================== Breakpoint transitions ========================

  const t_set_breakpoint = Transition.builder('t_set_breakpoint')
    .inputs(one(p.breakpoints), one(p.userSetBreakpoint.place))
    .outputs(outPlace(p.breakpoints))
    .timing(immediate())
    .action(async (ctx) => {
      const bpList = ctx.input(p.breakpoints) as BreakpointConfig[];
      const newBp = ctx.input(p.userSetBreakpoint.place) as BreakpointConfig;
      const updated = [...bpList, newBp];
      renderBreakpointList(updated);
      ctx.output(p.breakpoints, updated);
    })
    .build();

  const t_clear_breakpoint = Transition.builder('t_clear_breakpoint')
    .inputs(one(p.breakpoints), one(p.userClearBreakpoint.place))
    .outputs(outPlace(p.breakpoints))
    .timing(immediate())
    .action(async (ctx) => {
      const bpList = ctx.input(p.breakpoints) as BreakpointConfig[];
      const bpId = ctx.input(p.userClearBreakpoint.place) as string;
      const updated = bpList.filter(bp => bp.id !== bpId);
      renderBreakpointList(updated);
      ctx.output(p.breakpoints, updated);
    })
    .build();

  // ======================== Filter/search transitions ========================

  const t_apply_filter = Transition.builder('t_apply_filter')
    .inputs(one(p.filterState), one(p.userApplyFilter.place))
    .outputs(and(outPlace(p.filterState), outPlace(p.logDirty)))
    .timing(immediate())
    .action(async (ctx) => {
      const newFilter = ctx.input(p.userApplyFilter.place) as FilterState;
      ctx.output(p.filterState, newFilter);
      ctx.output(p.logDirty, undefined);
    })
    .build();

  const t_search = Transition.builder('t_search')
    .inputs(one(p.searchState), one(p.userSearch.place))
    .reads(p.uiState)
    .outputs(outPlace(p.searchState))
    .timing(immediate())
    .action(async (ctx) => {
      const term = ctx.input(p.userSearch.place) as string;
      const state = ctx.read(p.uiState) as UIState;
      const result = computeSearchMatches(term, state.events, state.eventIndex);
      updateSearchUI(result);
      ctx.output(p.searchState, result);
    })
    .build();

  const t_search_next = Transition.builder('t_search_next')
    .inputs(one(p.searchState), one(p.userSearchNext.place))
    .outputs(outPlace(p.searchState))
    .timing(immediate())
    .action(async (ctx) => {
      const current = ctx.input(p.searchState) as SearchState;
      const result = nextSearchMatch(current);
      updateSearchUI(result);
      ctx.output(p.searchState, result);
    })
    .build();

  const t_search_prev = Transition.builder('t_search_prev')
    .inputs(one(p.searchState), one(p.userSearchPrev.place))
    .outputs(outPlace(p.searchState))
    .timing(immediate())
    .action(async (ctx) => {
      const current = ctx.input(p.searchState) as SearchState;
      const result = prevSearchMatch(current);
      updateSearchUI(result);
      ctx.output(p.searchState, result);
    })
    .build();

  // ======================== Speed transition ========================

  const t_set_speed = Transition.builder('t_set_speed')
    .inputs(one(p.userSetSpeed.place))
    .timing(immediate())
    .action(async (ctx) => {
      const speed = ctx.input(p.userSetSpeed.place) as number;
      shared.playback.speed = speed;
      updateSpeedButtons(speed);
    })
    .build();

  // ======================== Reset zoom transition ========================

  // This doesn't need to be in the net, handled directly by DOM binding

  // ======================== Archive transitions ========================

  const t_open_archive_browser = Transition.builder('t_open_archive_browser')
    .inputs(one(p.userOpenArchiveBrowser.place))
    .reads(p.connected)
    .timing(immediate())
    .action(async () => {
      requestArchiveList();
    })
    .build();

  const t_on_archive_list = Transition.builder('t_on_archive_list')
    .inputs(one(p.wsMessage.place, (msg: DebugResponse) => msg.type === 'archiveList'))
    .timing(immediate())
    .action(async (ctx) => {
      const msg = ctx.input(p.wsMessage.place) as Extract<DebugResponse, { type: 'archiveList' }>;
      renderArchiveList(msg.archives);
      showArchiveBrowser(msg.storageAvailable);
    })
    .build();

  const t_import_archive = Transition.builder('t_import_archive')
    .inputs(one(p.userImportArchive.place))
    .reads(p.connected)
    .timing(immediate())
    .action(async (ctx) => {
      const sessionId = ctx.input(p.userImportArchive.place) as string;
      requestImportArchive(sessionId);
    })
    .build();

  const t_upload_archive = Transition.builder('t_upload_archive')
    .inputs(one(p.userUploadArchive.place))
    .reads(p.connected)
    .timing(immediate())
    .action(async (ctx) => {
      const file = ctx.input(p.userUploadArchive.place) as File;
      uploadArchiveFile(file);
    })
    .build();

  const t_on_archive_imported = Transition.builder('t_on_archive_imported')
    .inputs(one(p.wsMessage.place, (msg: DebugResponse) => msg.type === 'archiveImported'))
    .timing(immediate())
    .action(async (ctx) => {
      const msg = ctx.input(p.wsMessage.place) as Extract<DebugResponse, { type: 'archiveImported' }>;
      hideArchiveBrowser();
      executor.injectValue(p.userSelectSession, { sessionId: msg.sessionId, mode: 'replay' });
    })
    .build();

  // ======================== Net-name filter transition ========================

  const t_filter_net_name = Transition.builder('t_filter_net_name')
    .inputs(one(p.userFilterNetName.place))
    .timing(immediate())
    .action(async (ctx) => {
      const filter = ctx.input(p.userFilterNetName.place) as string;
      shared.netNameFilter = filter;
      populateSessionList(shared.allSessions, filter || undefined);
    })
    .build();

  // ======================== Build Net ========================

  const net = PetriNet.builder('DebugUI')
    .transitions(
      t_connect, t_on_open, t_on_close_connecting, t_on_close_connected, t_reconnect,
      t_subscribe, t_unsubscribe_and_switch, t_on_subscribed,
      t_on_session_list, t_on_event, t_on_event_batch, t_on_marking_snapshot,
      t_on_playback_state, t_on_breakpoint_hit, t_on_bp_list, t_on_bp_set,
      t_on_bp_cleared, t_on_filter_applied, t_on_unsubscribed, t_on_error,
      t_render_dot,
      t_fan_out_dirty, t_update_highlighting, t_update_event_log, t_update_marking,
      t_replay_play, t_replay_auto_step, t_replay_pause, t_replay_breakpoint_stop, t_replay_play_from_bp,
      t_replay_step_fwd, t_replay_step_back,
      t_replay_seek, t_replay_restart, t_replay_run_to_end,
      t_live_pause, t_live_resume, t_live_step_fwd, t_live_step_back,
      t_inspect_place,
      t_open_modal, t_close_modal,
      t_set_breakpoint, t_clear_breakpoint,
      t_apply_filter, t_search, t_search_next, t_search_prev,
      t_set_speed,
      t_open_archive_browser, t_on_archive_list, t_import_archive,
      t_upload_archive, t_on_archive_imported, t_filter_net_name,
    )
    .build();

  // ======================== Initial Tokens ========================

  const emptyFilterState: FilterState = { eventTypes: [], transitionNames: [], placeNames: [], filteredIndices: null };
  const emptySearchState: SearchState = { searchTerm: '', matches: [], currentMatchIndex: -1 };

  const initialTokens = new Map<Place<unknown>, Token<unknown>[]>([
    [p.idle, [tokenOf(undefined)]],
    [p.noSession, [tokenOf(undefined)]],
    [p.modalClosed, [tokenOf(undefined)]],
    [p.breakpoints, [tokenOf([] as BreakpointConfig[])]],
    [p.filterState, [tokenOf(emptyFilterState)]],
    [p.searchState, [tokenOf(emptySearchState)]],
  ]);

  return { net, initialTokens };
}

