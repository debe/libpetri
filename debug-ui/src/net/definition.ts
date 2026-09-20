/**
 * Debug UI Petri net definition.
 *
 * Builds the CTPN whose execution IS the debug UI behavior.
 * Environment places receive DOM events and WebSocket messages.
 * Transition actions perform DOM updates and WebSocket I/O.
 */

import {
  PetriNet, Transition, tokenOf,
  one, all, outPlace, and, xor,
  immediate, delayed,
  type BitmapNetExecutor, type EnvironmentPlace, type Place, type Token,
} from 'libpetri';
import * as p from './places.js';
import type { UIState, SessionData, FilterState, SearchState, DeadLetter } from './types.js';
import type { BreakpointConfig, NetEventInfo } from '../protocol/index.js';
import { shared, sendCommand } from './shared-state.js';
import { createWebSocket, setConnected, setDisconnected, setConnecting } from './actions/connection.js';
import {
  refreshSessions, populateSessionList, subscribeToSession, unsubscribeFromSession,
  buildSessionData, buildInitialUIState, applyMarkingSnapshot,
  enableControls, updateAutocompleteOptions,
} from './actions/session.js';
import {
  requestArchiveList, renderArchiveList, showArchiveBrowser, hideArchiveBrowser,
  requestImportArchive, uploadArchiveFile,
} from './actions/archive.js';
import { renderDotDiagram, updateDiagramHighlighting, toggleSubnetMode } from './actions/diagram.js';
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
import { setSubnetInstances, refreshSubnetPanel } from './actions/subnet-panel.js';

/**
 * What `t_log_dead_letter` writes. A frame nobody understands and a handler that threw are
 * defects and warn; a message that arrived for a session already left is routine.
 */
function logDeadLetter(letter: DeadLetter): void {
  const expected = letter.reason === 'no-session' || letter.reason === 'not-subscribing';
  const log = expected ? console.debug : console.warn;
  if (letter.error === undefined) {
    log(`Debug message dead-lettered (${letter.reason}):`, letter.message);
  } else {
    log(`Debug message dead-lettered (${letter.reason}):`, letter.message, letter.error);
  }
}

/**
 * Runs a UI side effect the net's next marking does not depend on. A throw is logged and goes
 * no further: the executor does not give a failed transition its inputs back, so an exception
 * that escaped here would take the transition's tokens with it.
 */
function attempt(transition: string, effect: () => void): void {
  try {
    effect();
  } catch (error) {
    console.error(`${transition}: UI update failed`, error);
  }
}

/** A `uiState` to emit, and how to undo what computing it changed outside the net. */
interface Fold {
  readonly next: UIState;
  /** Must not throw. */
  readonly undo?: () => void;
}

/**
 * Reference to the executor, set after creation. Actions use it for two things only, both of
 * them the outside world arriving: the WebSocket's callbacks, and the playback timer's tick.
 * Everything an action decides leaves through its declared outputs.
 */
let executor: BitmapNetExecutor;

export function setExecutor(exec: BitmapNetExecutor): void {
  executor = exec;
}

/**
 * Builds the debug UI PetriNet.
 *
 * Initial tokens: idle(1), noSession(1), routerReady(1), filterState(1),
 * modalClosed(1), breakpoints(1), searchState(1)
 *
 * Every action decides first and emits afterwards, and none lets an exception escape while it
 * holds a token the rest of the net waits on (`uiState`, `breakpoints`, the router's permit,
 * the session phase): the executor consumes inputs before the action runs and does not restore
 * them when it fails.
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
    // No socket could be created: wait and try again, as after a close.
    .outputs(xor(outPlace(p.connecting), outPlace(p.waitReconnect)))
    .timing(immediate())
    .action(async (ctx) => {
      try {
        setConnecting();
        createWebSocket(executor);
      } catch (error) {
        console.error('t_connect: no WebSocket, retrying', error);
        ctx.output(p.waitReconnect, undefined);
        return;
      }
      ctx.output(p.connecting, undefined);
    })
    .build();

  const t_on_open = Transition.builder('t_on_open')
    .inputs(one(p.connecting), one(p.wsOpenSignal.place))
    .outputs(outPlace(p.connected))
    .timing(immediate())
    .action(async (ctx) => {
      attempt('t_on_open', () => {
        setConnected();
        refreshSessions();
      });
      ctx.output(p.connected, undefined);
    })
    .build();

  const t_on_close_connecting = Transition.builder('t_on_close_connecting')
    .inputs(one(p.connecting), one(p.wsCloseSignal.place))
    .outputs(outPlace(p.waitReconnect))
    .timing(immediate())
    .action(async (ctx) => {
      attempt('t_on_close_connecting', setDisconnected);
      ctx.output(p.waitReconnect, undefined);
    })
    .build();

  const t_on_close_connected = Transition.builder('t_on_close_connected')
    .inputs(one(p.connected), one(p.wsCloseSignal.place))
    .outputs(outPlace(p.waitReconnect))
    .timing(immediate())
    .action(async (ctx) => {
      attempt('t_on_close_connected', setDisconnected);
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
  //
  // The session is in exactly one phase, and a subscribed session in exactly one mode:
  //
  //   noSession + subscribing + subscribedSession = 1
  //   subscribedSession = liveSession + replaySession
  //   replaySession     = replayPaused + replayPlaying + breakpointPaused
  //   uiState           = subscribedSession
  //
  // `t_on_subscribed` (below, in the router) emits a session's tokens as one XOR leg, and one of
  // the four `t_switch_from_*` transitions takes all of them back: which one is decided by what
  // the marking holds, so a session cannot be left with part of it still marked.

  const t_subscribe = Transition.builder('t_subscribe')
    .inputs(one(p.noSession), one(p.userSelectSession.place))
    .reads(p.connected)
    .outputs(xor(outPlace(p.subscribing), outPlace(p.noSession)))
    .timing(immediate())
    .action(async (ctx) => {
      const selection = ctx.input(p.userSelectSession.place);
      try {
        subscribeToSession(selection.sessionId, selection.mode);
      } catch (error) {
        console.error(`t_subscribe: could not subscribe to ${selection.sessionId}`, error);
        ctx.output(p.noSession, undefined);
        return;
      }
      ctx.output(p.subscribing, selection.sessionId);
    })
    .build();

  /** Leaves the subscribed session, whose mode tokens are `held`, for the one just selected. */
  function switchFrom(name: string, ...held: Place<unknown>[]): Transition {
    return Transition.builder(name)
      .inputs(one(p.subscribedSession), one(p.userSelectSession.place), one(p.uiState), ...held.map(place => one(place)))
      .reads(p.connected)
      // If the commands cannot be sent there is no answer to wait for in `subscribing`.
      .outputs(xor(outPlace(p.subscribing), outPlace(p.noSession)))
      .timing(immediate())
      .action(async (ctx) => {
        const oldSessionId = ctx.input(p.subscribedSession);
        const selection = ctx.input(p.userSelectSession.place);
        // The old session is gone either way: its tokens are consumed.
        stopPlayback();
        shared.currentSession = null;
        shared.currentMode = null;
        shared.replay = { allEvents: [], checkpoints: [], checkpointInterval: 20 };
        try {
          unsubscribeFromSession(oldSessionId);
          subscribeToSession(selection.sessionId, selection.mode);
        } catch (error) {
          console.error(`${name}: could not switch to ${selection.sessionId}`, error);
          attempt(name, () => enableControls(false));
          ctx.output(p.noSession, undefined);
          return;
        }
        ctx.output(p.subscribing, selection.sessionId);
      })
      .build();
  }

  const t_switch_from_live = switchFrom('t_switch_from_live', p.liveSession);
  const t_switch_from_replay_paused = switchFrom('t_switch_from_replay_paused', p.replaySession, p.replayPaused);
  const t_switch_from_replay_playing = switchFrom('t_switch_from_replay_playing', p.replaySession, p.replayPlaying);
  const t_switch_from_breakpoint = switchFrom('t_switch_from_breakpoint', p.replaySession, p.breakpointPaused);

  // The connection closed with a subscribe outstanding: its answer died with the socket, and
  // nothing else leaves `subscribing`. `connected` is consumed only by `t_on_close_connected`
  // and never held by a firing, so its absence means what it says. (A *subscribed* session is
  // deliberately kept across a close: the net under debug has usually just exited, and its last
  // state is what the user came to look at.)
  const t_abandon_subscribe = Transition.builder('t_abandon_subscribe')
    .inputs(one(p.subscribing))
    .inhibitor(p.connected)
    .outputs(outPlace(p.noSession))
    .timing(immediate())
    .action(async (ctx) => {
      ctx.output(p.noSession, undefined);
    })
    .build();

  // ======================== Message router ========================
  //
  // `wsMessage` carries every protocol message. Which handler takes one is decided by
  // `t_route_message`'s XOR output, one leg per message type plus the dead-letter leg, so the
  // decision is part of the topology: exported, drawn and verified like any other arc. (Input
  // guards used to make it, one predicate per handler; they left the core with IO-006.)
  //
  //   wsMessage + routerReady ──t_route_message──▶ msgSessionList | msgSubscribed | … | deadLetter
  //   msgX (+ what the handler needs) ──t_on_x──▶ routerReady (+ its results)   | deadLetter
  //   msgX, inhibited by the place t_on_x needs ──t_drop_x──▶ deadLetter
  //   deadLetter ──t_log_dead_letter──▶ routerReady
  //
  // `routerReady` is a one-token permit: the classifier takes it, whoever consumes the routed
  // message hands it back. One message is between `wsMessage` and its handler at a time, so
  // messages are handled in arrival order across types — an `event` never overtakes the
  // `markingSnapshot` before it. No priorities are involved.
  //
  // Because the router is serial, every routed message needs a consumer in every session
  // state, or the head of the queue blocks the rest. The handlers with a session precondition
  // therefore have a complement, `t_drop_*`, inhibited by exactly the place the handler
  // requires. And because a lost permit would stop the UI for good, no handler lets an
  // exception escape: it decides first, then emits one complete XOR leg — its results, or the
  // resource tokens it took, unchanged, plus a dead letter. The same holds for every *other*
  // transition that takes `uiState` or `breakpoints` (the replay commands, the breakpoint
  // edits): a handler waiting on a token that never comes back holds the permit just as well.

  const routeOf = new Map<string, Place<unknown>>(Object.entries(p.messageRoutes));

  const t_route_message = Transition.builder('t_route_message')
    .inputs(one(p.wsMessage.place), one(p.routerReady))
    .outputs(xor(...[...routeOf.values()].map(route => outPlace(route)), outPlace(p.deadLetter)))
    .timing(immediate())
    .action(async (ctx) => {
      // The frame is whatever JSON.parse returned; nothing about it is known yet.
      const frame: unknown = ctx.input(p.wsMessage.place);
      const type = typeof frame === 'object' && frame !== null ? (frame as { type?: unknown }).type : undefined;
      // A Map, not an object: `__proto__` and `constructor` are not routes.
      const route = typeof type === 'string' ? routeOf.get(type) : undefined;
      if (route) {
        ctx.output(route, frame);
      } else {
        ctx.output(p.deadLetter, { reason: 'unknown-type', message: frame });
      }
    })
    .build();

  /** A handler with no precondition and no result: consume the message, hand the permit back. */
  function onMessage<M>(name: string, from: Place<M>, handle: (msg: M) => void): Transition {
    return Transition.builder(name)
      .inputs(one(from))
      .outputs(xor(outPlace(p.routerReady), outPlace(p.deadLetter)))
      .timing(immediate())
      .action(async (ctx) => {
        const msg = ctx.input(from);
        try {
          handle(msg);
        } catch (error) {
          ctx.output(p.deadLetter, { reason: 'handler-failed', message: msg, error });
          return;
        }
        ctx.output(p.routerReady, undefined);
      })
      .build();
  }

  /**
   * A handler that folds a message into `uiState`. It needs a subscribed session — of mode
   * `mode`, if the fold depends on it — and without one the message goes to
   * {@link dropWithout}'s transition instead.
   */
  function onSessionMessage<M>(
    name: string, from: Place<M>, mode: Place<SessionData> | null,
    fold: (state: UIState, msg: M) => UIState | Fold,
  ): Transition {
    return Transition.builder(name)
      .inputs(one(from), one(p.uiState))
      .reads(p.subscribedSession, ...(mode ? [mode] : []))
      .outputs(xor(
        and(outPlace(p.uiState), outPlace(p.stateDirty), outPlace(p.routerReady)),
        and(outPlace(p.uiState), outPlace(p.deadLetter)),
      ))
      .timing(immediate())
      .action(async (ctx) => {
        const msg = ctx.input(from);
        const state = ctx.input(p.uiState);
        let folded: Fold | undefined;
        try {
          const result = fold(state, msg);
          folded = 'next' in result ? result : { next: result };
          updateTimelinePosition(folded.next.eventIndex, folded.next.totalEvents);
        } catch (error) {
          folded?.undo?.();
          ctx.output(p.uiState, state);
          ctx.output(p.deadLetter, { reason: 'handler-failed', message: msg, error });
          return;
        }
        ctx.output(p.uiState, folded.next);
        ctx.output(p.stateDirty, undefined);
        ctx.output(p.routerReady, undefined);
      })
      .build();
  }

  /** The complement of a handler that requires `required`: enabled exactly while it is empty. */
  function dropWithout<M>(name: string, from: Place<M>, required: Place<unknown>, reason: DeadLetter['reason']): Transition {
    return Transition.builder(name)
      .inputs(one(from))
      .inhibitor(required)
      .outputs(outPlace(p.deadLetter))
      .timing(immediate())
      .action(async (ctx) => {
        ctx.output(p.deadLetter, { reason, message: ctx.input(from) });
      })
      .build();
  }

  const t_log_dead_letter = Transition.builder('t_log_dead_letter')
    .inputs(one(p.deadLetter))
    .outputs(outPlace(p.routerReady))
    .timing(immediate())
    .action(async (ctx) => {
      const letter = ctx.input(p.deadLetter);
      try {
        logDeadLetter(letter);
      } catch {
        // Logging must not cost the permit.
      }
      ctx.output(p.routerReady, undefined);
    })
    .build();

  // ---- session -----------------------------------------------------------------------

  const t_on_subscribed = Transition.builder('t_on_subscribed')
    .inputs(one(p.msgSubscribed), one(p.subscribing))
    .outputs(xor(
      and(outPlace(p.subscribedSession), outPlace(p.liveSession),
        outPlace(p.uiState), outPlace(p.dotSource), outPlace(p.stateDirty), outPlace(p.routerReady)),
      and(outPlace(p.subscribedSession), outPlace(p.replaySession), outPlace(p.replayPaused),
        outPlace(p.uiState), outPlace(p.dotSource), outPlace(p.stateDirty), outPlace(p.routerReady)),
      // The subscribe did not take: back to noSession, so the user can select again.
      and(outPlace(p.noSession), outPlace(p.deadLetter)),
    ))
    .timing(immediate())
    .action(async (ctx) => {
      const msg = ctx.input(p.msgSubscribed);
      const requested = ctx.input(p.subscribing);
      let sessionData: SessionData;
      let initialState: UIState;
      let isReplay: boolean;
      try {
        // What can fail without having touched anything comes first.
        sessionData = buildSessionData(msg);
        isReplay = sessionData.mode === 'replay';
        initialState = buildInitialUIState(msg, isReplay);

        enableControls(true);
        updateAutocompleteOptions(sessionData.structure);
        updatePlaybackControls(isReplay);
        updateTimelinePosition(initialState.eventIndex, initialState.totalEvents);
        setSubnetInstances(msg.subnetInstances);
      } catch (error) {
        // Undo what is on screen, and tell the server: it believes the subscribe took and
        // would go on streaming a session nobody shows.
        attempt('t_on_subscribed', () => enableControls(false));
        attempt('t_on_subscribed', () => unsubscribeFromSession(requested));
        ctx.output(p.noSession, undefined);
        ctx.output(p.deadLetter, { reason: 'handler-failed', message: msg, error });
        return;
      }

      // Past this point nothing throws.
      shared.replay = { allEvents: [], checkpoints: [], checkpointInterval: 20 };
      shared.currentSession = sessionData;
      shared.currentMode = isReplay ? 'replay' : 'live';

      ctx.output(p.subscribedSession, msg.sessionId);
      if (isReplay) {
        ctx.output(p.replaySession, sessionData);
        ctx.output(p.replayPaused, undefined);
      } else {
        ctx.output(p.liveSession, sessionData);
      }
      ctx.output(p.uiState, initialState);
      ctx.output(p.dotSource, msg.dotDiagram);
      ctx.output(p.stateDirty, undefined);
      ctx.output(p.routerReady, undefined);
    })
    .build();

  // `subscribed` with no subscribe outstanding answers nothing. Left waiting, it would be taken
  // for the answer to the *next* subscribe, whichever session that asks for.
  const t_drop_subscribed = dropWithout('t_drop_subscribed', p.msgSubscribed, p.subscribing, 'not-subscribing');

  const t_on_unsubscribed = onMessage('t_on_unsubscribed', p.msgUnsubscribed, () => {
    // Cleanup handled by the switch transitions
  });

  function showSessionList(msg: p.ResponseOf<'sessionList'>): void {
    shared.allSessions = [...msg.sessions];
    populateSessionList(msg.sessions, shared.netNameFilter || undefined);
  }

  // The page was opened with `?sessionId=`: the first list to arrive spends the deep link, and
  // selects that session if it names it. "Use the link if there is one" is a pair of
  // transitions, not a read arc: one takes the link, the other is inhibited by it.
  const t_on_session_list = Transition.builder('t_on_session_list')
    .inputs(one(p.msgSessionList))
    .inhibitor(p.deepLink.place)
    .outputs(xor(outPlace(p.routerReady), outPlace(p.deadLetter)))
    .timing(immediate())
    .action(async (ctx) => {
      const msg = ctx.input(p.msgSessionList);
      try {
        showSessionList(msg);
      } catch (error) {
        ctx.output(p.deadLetter, { reason: 'handler-failed', message: msg, error });
        return;
      }
      ctx.output(p.routerReady, undefined);
    })
    .build();

  const t_on_session_list_deep_link = Transition.builder('t_on_session_list_deep_link')
    .inputs(one(p.msgSessionList), one(p.deepLink.place))
    .outputs(xor(
      and(outPlace(p.routerReady), outPlace(p.userSelectSession.place)),
      outPlace(p.routerReady),
      outPlace(p.deadLetter),
    ))
    .timing(immediate())
    .action(async (ctx) => {
      const msg = ctx.input(p.msgSessionList);
      const target = ctx.input(p.deepLink.place);
      let found: boolean;
      try {
        showSessionList(msg);
        found = msg.sessions.some(session => session.sessionId === target);
      } catch (error) {
        ctx.output(p.deadLetter, { reason: 'handler-failed', message: msg, error });
        return;
      }
      ctx.output(p.routerReady, undefined);
      if (found) ctx.output(p.userSelectSession.place, { sessionId: target, mode: 'replay' });
    })
    .build();

  // ---- session state -----------------------------------------------------------------
  //
  // Without a subscribed session there is no uiState to fold these into. They belong to the
  // session that was just left, so they are dropped rather than kept for the one that follows.
  // The inhibitor is on `subscribedSession`, not on `uiState`: uiState is also absent while a
  // replay step or a seek holds it, and a message must wait that out, not be dropped.

  const t_on_event = onSessionMessage('t_on_event', p.msgEvent, null, (state, msg) => ({
    ...applyEventToState(state, msg.event),
    events: [...state.events, msg.event],
    eventIndex: msg.index + 1,
    totalEvents: Math.max(state.totalEvents, msg.index + 1),
  }));
  const t_drop_event = dropWithout('t_drop_event', p.msgEvent, p.subscribedSession, 'no-session');

  // A batch means different things to the two modes, and which one applies is the marking's
  // to say: a live session follows the batch, a replay session only stores it.
  const t_on_event_batch = onSessionMessage('t_on_event_batch', p.msgEventBatch, p.liveSession, (state, msg) => {
    let updated = state;
    for (const event of msg.events) {
      updated = applyEventToState(updated, event);
    }
    return {
      ...updated,
      events: [...state.events, ...msg.events],
      eventIndex: msg.startIndex + msg.events.length,
      totalEvents: Math.max(state.totalEvents, msg.startIndex + msg.events.length),
    };
  });

  const t_on_replay_event_batch = onSessionMessage('t_on_replay_event_batch', p.msgEventBatch, p.replaySession, (state, msg) => {
    // The replay buffer lives outside the net and is appended to in place (a replay is
    // hundreds of batches; copying it per batch is quadratic). So this fold can be undone.
    const events = shared.replay.allEvents;
    const previousLength = events.length;
    const previousCheckpoints = shared.replay.checkpoints;
    const undo = () => {
      events.length = previousLength;
      shared.replay.checkpoints = previousCheckpoints;
    };
    try {
      for (const event of msg.events) events.push(event);
      shared.replay.checkpoints = buildCheckpoints(events, previousLength);
    } catch (error) {
      undo();
      throw error;
    }
    return { next: { ...state, events, totalEvents: events.length }, undo };
  });
  const t_drop_event_batch = dropWithout('t_drop_event_batch', p.msgEventBatch, p.subscribedSession, 'no-session');

  const t_on_marking_snapshot = onSessionMessage('t_on_marking_snapshot', p.msgMarkingSnapshot, null, applyMarkingSnapshot);
  const t_drop_marking_snapshot = dropWithout('t_drop_marking_snapshot', p.msgMarkingSnapshot, p.subscribedSession, 'no-session');

  // ---- playback and breakpoints ------------------------------------------------------

  const t_on_playback_state = onMessage('t_on_playback_state', p.msgPlaybackState, (msg) => {
    updatePlaybackControls(msg.paused);
    shared.playback.speed = msg.speed;
    updateSpeedButtons(msg.speed);
  });

  const t_on_breakpoint_hit = onMessage('t_on_breakpoint_hit', p.msgBreakpointHit, (msg) => {
    updatePlaybackControls('breakpoint');
    highlightBreakpointInList(msg.breakpointId);
  });

  const t_on_bp_list = Transition.builder('t_on_bp_list')
    .inputs(one(p.msgBreakpointList), one(p.breakpoints))
    .outputs(xor(
      and(outPlace(p.breakpoints), outPlace(p.routerReady)),
      and(outPlace(p.breakpoints), outPlace(p.deadLetter)),
    ))
    .timing(immediate())
    .action(async (ctx) => {
      const msg = ctx.input(p.msgBreakpointList);
      const current = ctx.input(p.breakpoints);
      let next: BreakpointConfig[];
      try {
        next = [...msg.breakpoints];
        renderBreakpointList(msg.breakpoints);
        // Keep the per-instance breakpoint toggle in sync with server state.
        refreshSubnetPanel();
      } catch (error) {
        ctx.output(p.breakpoints, current);
        ctx.output(p.deadLetter, { reason: 'handler-failed', message: msg, error });
        return;
      }
      ctx.output(p.breakpoints, next);
      ctx.output(p.routerReady, undefined);
    })
    .build();

  // Confirmations: the UI was already updated optimistically.
  const t_on_bp_set = onMessage('t_on_bp_set', p.msgBreakpointSet, () => {});
  const t_on_bp_cleared = onMessage('t_on_bp_cleared', p.msgBreakpointCleared, () => {});
  const t_on_filter_applied = onMessage('t_on_filter_applied', p.msgFilterApplied, () => {});

  const t_on_error = onMessage('t_on_error', p.msgError, (msg) => {
    console.error(`Debug protocol error [${msg.code}]: ${msg.message}`);
  });

  // ======================== Diagram transitions ========================

  const t_render_dot = Transition.builder('t_render_dot')
    .inputs(one(p.dotSource))
    // A new diagram is being drawn: the old one is no longer there to highlight.
    .reset(p.svgReady)
    .outputs(outPlace(p.svgReady))
    .timing(immediate())
    .action(async (ctx) => {
      const dot = ctx.input(p.dotSource);
      await renderDotDiagram(dot);
      ctx.output(p.svgReady, undefined);
    })
    .build();

  const t_toggle_subnets = Transition.builder('t_toggle_subnets')
    .inputs(one(p.userToggleSubnets.place))
    .outputs(outPlace(p.highlightDirty))
    .timing(immediate())
    .action(async (ctx) => {
      try {
        await toggleSubnetMode();
      } catch (error) {
        console.error('t_toggle_subnets: UI update failed', error);
      }
      // Re-mount cleared the SVG highlights; re-apply against the new cache.
      ctx.output(p.highlightDirty, undefined);
    })
    .build();

  // ======================== Repaint ========================
  //
  //   stateDirty ──t_fan_out_dirty──▶ highlightDirty + logDirty + markingDirty
  //   rafTick (all), reads uiState ──t_frame──▶ frameHighlight + frameLog + frameMarking
  //   rafTick (all), no uiState    ──t_idle_frame──▶ ∅
  //   xDirty (all) + frameX ──t_update_x──▶ ∅         repaint
  //   frameX, no xDirty     ──t_skip_x──▶ ∅           nothing to repaint this frame
  //
  // "Dirty" is a fact, not a count, and so is "a frame came": both are taken with `all()`, so a
  // burst of events costs each panel one repaint on the next frame, not one per event. Every
  // frame gives each panel its own token — they used to share the one `rafTick` and take turns —
  // and a panel with nothing to do consumes its token rather than leaving it, so ticks do not
  // pile up while the UI is idle and pay for unthrottled repaints later. Skipping is always
  // safe: the dirty flag stays until a repaint takes it.

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

  const t_frame = Transition.builder('t_frame')
    .inputs(all(p.rafTick.place))
    .reads(p.uiState)
    .outputs(and(outPlace(p.frameHighlight), outPlace(p.frameLog), outPlace(p.frameMarking)))
    .timing(immediate())
    .action(async (ctx) => {
      ctx.output(p.frameHighlight, undefined);
      ctx.output(p.frameLog, undefined);
      ctx.output(p.frameMarking, undefined);
    })
    .build();

  // No state to paint: no session, or a transition holds uiState for this instant.
  const t_idle_frame = Transition.builder('t_idle_frame')
    .inputs(all(p.rafTick.place))
    .inhibitor(p.uiState)
    .timing(immediate())
    .build();

  /** The complement of a repaint: this panel's frame token, while the panel is not `dirty`. */
  function skipFrame(name: string, frame: Place<void>, missing: Place<unknown>): Transition {
    return Transition.builder(name)
      .inputs(one(frame))
      .inhibitor(missing)
      .timing(immediate())
      .build();
  }

  const t_update_highlighting = Transition.builder('t_update_highlighting')
    .inputs(all(p.highlightDirty), one(p.frameHighlight))
    .reads(p.svgReady, p.uiState)
    .timing(immediate())
    .action(async (ctx) => {
      const state = ctx.read(p.uiState);
      const session = shared.currentSession;
      updateDiagramHighlighting(state, session);
    })
    .build();
  const t_skip_highlighting = skipFrame('t_skip_highlighting', p.frameHighlight, p.highlightDirty);
  // Dirty, but the diagram is still being drawn: the flag waits for it, the frame does not.
  const t_await_diagram = skipFrame('t_await_diagram', p.frameHighlight, p.svgReady);

  const t_update_event_log = Transition.builder('t_update_event_log')
    .inputs(all(p.logDirty), one(p.frameLog))
    .reads(p.uiState, p.filterState)
    .timing(immediate())
    .action(async (ctx) => {
      const state = ctx.read(p.uiState);
      const filter = ctx.read(p.filterState);
      renderVisibleEvents(state, filter);
    })
    .build();
  const t_skip_event_log = skipFrame('t_skip_event_log', p.frameLog, p.logDirty);

  const t_update_marking = Transition.builder('t_update_marking')
    .inputs(all(p.markingDirty), one(p.frameMarking))
    .reads(p.uiState)
    .timing(immediate())
    .action(async (ctx) => {
      const state = ctx.read(p.uiState);
      const session = shared.currentSession;
      updateMarkingInspector(state, session);
    })
    .build();
  const t_skip_marking = skipFrame('t_skip_marking', p.frameMarking, p.markingDirty);

  // ======================== Replay playback transitions ========================
  //
  //   replayPaused + userClickPlay     ──t_replay_play──────────▶ replayPlaying + autoStepTick
  //   breakpointPaused + userClickPlay ──t_replay_play_from_bp──▶ replayPlaying + autoStepTick
  //   autoStepTick + replayPlaying + uiState ──t_replay_auto_step──▶
  //         uiState' + stateDirty + replayPlaying    stepped; the timer for the next tick is armed
  //       | uiState + replayPaused                   the end of the replay (or the step failed)
  //       | uiState + breakpointPaused               the next event hits a breakpoint
  //   replayPlaying + userClickPause ──t_replay_pause──▶ replayPaused
  //   autoStepTick, no replayPlaying ──t_drop_stale_tick──▶ ∅
  //
  // The step decides where playback goes and says so with its output leg. (It used to peek at
  // the marking through the executor and inject a pause click, a breakpoint signal or a step
  // click for other transitions to find.) The clock stays outside: a tick is time passing, and
  // it enters through `autoStepTick` like any other event. A tick that finds nothing playing is
  // consumed at once, so none is left to run beside the first tick of the next play.

  /** Arms the timer whose tick is the next step. One timer at a time, whatever ticks arrive. */
  function armNextTick(): void {
    stopPlayback();
    shared.playback.timer = setTimeout(() => {
      shared.playback.timer = null;
      executor.injectNoAwait(p.autoStepTick, undefined);
    }, calculatePlaybackDelay(shared.playback.speed));
  }

  function startPlaying(name: string, from: Place<void>): Transition {
    return Transition.builder(name)
      .inputs(one(from), one(p.userClickPlay.place))
      .reads(p.replaySession)
      .outputs(and(outPlace(p.replayPlaying), outPlace(p.autoStepTick.place)))
      .timing(immediate())
      .action(async (ctx) => {
        attempt(name, () => updatePlaybackControls(false));
        ctx.output(p.replayPlaying, undefined);
        ctx.output(p.autoStepTick.place, undefined);
      })
      .build();
  }

  const t_replay_play = startPlaying('t_replay_play', p.replayPaused);
  const t_replay_play_from_bp = startPlaying('t_replay_play_from_bp', p.breakpointPaused);

  /** State after the event at `state.eventIndex`. */
  function stepForward(state: UIState, events: readonly NetEventInfo[]): UIState {
    return {
      ...applyEventToState(state, events[state.eventIndex]!),
      eventIndex: state.eventIndex + 1,
      totalEvents: events.length,
    };
  }

  const t_replay_auto_step = Transition.builder('t_replay_auto_step')
    .inputs(one(p.autoStepTick.place), one(p.replayPlaying), one(p.uiState))
    .reads(p.breakpoints)
    .outputs(xor(
      and(outPlace(p.uiState), outPlace(p.stateDirty), outPlace(p.replayPlaying)),
      and(outPlace(p.uiState), outPlace(p.replayPaused)),
      and(outPlace(p.uiState), outPlace(p.breakpointPaused)),
    ))
    .timing(immediate())
    .action(async (ctx) => {
      const state = ctx.input(p.uiState);
      let decision: { leg: 'step' | 'end' | 'breakpoint'; state: UIState };
      try {
        const events = shared.replay.allEvents;
        // A breakpoint stops playback *before* its event; resuming from there must step past it.
        const hit = state.eventIndex < events.length && state.breakpointHitIndex !== state.eventIndex
          ? checkClientBreakpoints(events[state.eventIndex]!, ctx.read(p.breakpoints))
          : null;
        if (state.eventIndex >= events.length) {
          stopPlayback();
          updatePlaybackControls(true);
          decision = { leg: 'end', state };
        } else if (hit) {
          stopPlayback();
          highlightBreakpointInList(hit.id);
          updatePlaybackControls('breakpoint');
          decision = { leg: 'breakpoint', state: { ...state, breakpointHitIndex: state.eventIndex } };
        } else {
          const next = { ...stepForward(state, events), breakpointHitIndex: null };
          updateTimelinePosition(next.eventIndex, next.totalEvents);
          armNextTick();
          decision = { leg: 'step', state: next };
        }
      } catch (error) {
        console.error('t_replay_auto_step: step failed, playback paused', error);
        stopPlayback();
        attempt('t_replay_auto_step', () => updatePlaybackControls(true));
        decision = { leg: 'end', state };
      }

      ctx.output(p.uiState, decision.state);
      if (decision.leg === 'step') {
        ctx.output(p.stateDirty, undefined);
        ctx.output(p.replayPlaying, undefined);
      } else {
        ctx.output(decision.leg === 'end' ? p.replayPaused : p.breakpointPaused, undefined);
      }
    })
    .build();

  const t_replay_pause = Transition.builder('t_replay_pause')
    .inputs(one(p.replayPlaying), one(p.userClickPause.place))
    .outputs(outPlace(p.replayPaused))
    .timing(immediate())
    .action(async (ctx) => {
      stopPlayback();
      attempt('t_replay_pause', () => updatePlaybackControls(true));
      ctx.output(p.replayPaused, undefined);
    })
    .build();

  // `replayPlaying` is also absent for the instant `t_replay_auto_step` holds it. A tick that
  // arrives then is a second tick of the same play, and dropping it is just as right.
  const t_drop_stale_tick = Transition.builder('t_drop_stale_tick')
    .inputs(one(p.autoStepTick.place))
    .inhibitor(p.replayPlaying)
    .timing(immediate())
    .build();

  /**
   * A replay command that moves `uiState`. If `move` throws, the state goes back unchanged: the
   * router's handlers and the session switch wait on this token.
   */
  function onReplayCommand<I>(name: string, trigger: EnvironmentPlace<I>, move: (state: UIState, input: I) => UIState): Transition {
    return Transition.builder(name)
      .inputs(one(p.uiState), one(trigger.place))
      .reads(p.replaySession)
      .outputs(and(outPlace(p.uiState), outPlace(p.stateDirty)))
      .timing(immediate())
      .action(async (ctx) => {
        const state = ctx.input(p.uiState);
        let next: UIState;
        try {
          next = move(state, ctx.input(trigger.place));
          updateTimelinePosition(next.eventIndex, next.totalEvents);
        } catch (error) {
          console.error(`${name}: failed, state left unchanged`, error);
          next = state;
        }
        ctx.output(p.uiState, next);
        ctx.output(p.stateDirty, undefined);
      })
      .build();
  }

  const t_replay_step_fwd = onReplayCommand('t_replay_step_fwd', p.userClickStepFwd, (state) =>
    state.eventIndex < shared.replay.allEvents.length ? stepForward(state, shared.replay.allEvents) : state);

  // Seeking rebuilds the state from a checkpoint, which also forgets a breakpoint stopped at.
  const t_replay_step_back = onReplayCommand('t_replay_step_back', p.userClickStepBack, (state) =>
    state.eventIndex > 0 ? seekToIndex(state.eventIndex - 1) : { ...state, breakpointHitIndex: null });

  const t_replay_seek = onReplayCommand('t_replay_seek', p.userSeekSlider, (_state, targetIndex) => seekToIndex(targetIndex));

  const t_replay_restart = onReplayCommand('t_replay_restart', p.userClickRestart, () => seekToIndex(0));

  const t_replay_run_to_end = onReplayCommand('t_replay_run_to_end', p.userClickRunToEnd, () =>
    seekToIndex(shared.replay.allEvents.length));

  // ======================== Live mode control transitions ========================

  const t_live_pause = Transition.builder('t_live_pause')
    .inputs(one(p.userClickPause.place))
    .reads(p.liveSession)
    .timing(immediate())
    .action(async (ctx) => {
      const session = ctx.read(p.liveSession);
      sendCommand({ type: 'pause', sessionId: session.sessionId });
    })
    .build();

  const t_live_resume = Transition.builder('t_live_resume')
    .inputs(one(p.userClickPlay.place))
    .reads(p.liveSession)
    .timing(immediate())
    .action(async (ctx) => {
      const session = ctx.read(p.liveSession);
      sendCommand({ type: 'resume', sessionId: session.sessionId });
    })
    .build();

  const t_live_step_fwd = Transition.builder('t_live_step_fwd')
    .inputs(one(p.userClickStepFwd.place))
    .reads(p.liveSession)
    .timing(immediate())
    .action(async (ctx) => {
      const session = ctx.read(p.liveSession);
      sendCommand({ type: 'stepForward', sessionId: session.sessionId });
    })
    .build();

  const t_live_step_back = Transition.builder('t_live_step_back')
    .inputs(one(p.userClickStepBack.place))
    .reads(p.liveSession)
    .timing(immediate())
    .action(async (ctx) => {
      const session = ctx.read(p.liveSession);
      sendCommand({ type: 'stepBackward', sessionId: session.sessionId });
    })
    .build();

  // ======================== Inspector transitions ========================

  const t_inspect_place = Transition.builder('t_inspect_place')
    .inputs(one(p.userClickPlace.place))
    .reads(p.uiState)
    // One place is selected at a time: the selection before this one goes.
    .reset(p.selectedPlace)
    .outputs(outPlace(p.selectedPlace))
    .timing(immediate())
    .action(async (ctx) => {
      const raw = ctx.input(p.userClickPlace.place);
      // Resolve graphId (e.g. "p_start") to place name (e.g. "start") if needed
      const lookup = shared.currentSession?.byGraphId[raw];
      const placeName = lookup && !lookup.isTransition ? lookup.name : raw;
      const state = ctx.read(p.uiState);
      attempt('t_inspect_place', () => renderTokenInspector(placeName, state));
      ctx.output(p.selectedPlace, placeName);
    })
    .build();

  // ======================== Modal transitions ========================

  const t_open_modal = Transition.builder('t_open_modal')
    .inputs(one(p.modalClosed), one(p.userOpenModal.place))
    .outputs(outPlace(p.modalOpen))
    .timing(immediate())
    .action(async (ctx) => {
      const content = ctx.input(p.userOpenModal.place);
      attempt('t_open_modal', () => showModal(content));
      ctx.output(p.modalOpen, content);
    })
    .build();

  const t_close_modal = Transition.builder('t_close_modal')
    .inputs(one(p.modalOpen), one(p.userCloseModal.place))
    .outputs(outPlace(p.modalClosed))
    .timing(immediate())
    .action(async (ctx) => {
      attempt('t_close_modal', closeModal);
      ctx.output(p.modalClosed, undefined);
    })
    .build();

  // ======================== Breakpoint transitions ========================

  /**
   * An edit of the breakpoint list. If it throws, the list goes back unchanged: `t_on_bp_list`
   * waits on this token with the router's permit in hand, and playback reads it.
   */
  function onBreakpointEdit<I>(name: string, trigger: EnvironmentPlace<I>, edit: (list: BreakpointConfig[], input: I) => BreakpointConfig[]): Transition {
    return Transition.builder(name)
      .inputs(one(p.breakpoints), one(trigger.place))
      .outputs(outPlace(p.breakpoints))
      .timing(immediate())
      .action(async (ctx) => {
        const current = ctx.input(p.breakpoints);
        let next: BreakpointConfig[];
        try {
          next = edit(current, ctx.input(trigger.place));
          renderBreakpointList(next);
        } catch (error) {
          console.error(`${name}: failed, breakpoints left unchanged`, error);
          next = current;
        }
        ctx.output(p.breakpoints, next);
      })
      .build();
  }

  const t_set_breakpoint = onBreakpointEdit('t_set_breakpoint', p.userSetBreakpoint, (list, added) => [...list, added]);
  const t_clear_breakpoint = onBreakpointEdit('t_clear_breakpoint', p.userClearBreakpoint, (list, id) => list.filter(bp => bp.id !== id));

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

  /** The search state after `search`, shown; or `current`, if either throws. */
  function searched(transition: string, current: SearchState, search: () => SearchState): SearchState {
    try {
      const result = search();
      updateSearchUI(result);
      return result;
    } catch (error) {
      console.error(`${transition}: failed, search left unchanged`, error);
      return current;
    }
  }

  const t_search = Transition.builder('t_search')
    .inputs(one(p.searchState), one(p.userSearch.place))
    .reads(p.uiState)
    .outputs(outPlace(p.searchState))
    .timing(immediate())
    .action(async (ctx) => {
      const current = ctx.input(p.searchState);
      const term = ctx.input(p.userSearch.place);
      const state = ctx.read(p.uiState);
      ctx.output(p.searchState, searched('t_search', current, () => computeSearchMatches(term, state.events, state.eventIndex)));
    })
    .build();

  const t_search_next = Transition.builder('t_search_next')
    .inputs(one(p.searchState), one(p.userSearchNext.place))
    .outputs(outPlace(p.searchState))
    .timing(immediate())
    .action(async (ctx) => {
      const current = ctx.input(p.searchState);
      ctx.output(p.searchState, searched('t_search_next', current, () => nextSearchMatch(current)));
    })
    .build();

  const t_search_prev = Transition.builder('t_search_prev')
    .inputs(one(p.searchState), one(p.userSearchPrev.place))
    .outputs(outPlace(p.searchState))
    .timing(immediate())
    .action(async (ctx) => {
      const current = ctx.input(p.searchState);
      ctx.output(p.searchState, searched('t_search_prev', current, () => prevSearchMatch(current)));
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

  const t_on_archive_list = onMessage('t_on_archive_list', p.msgArchiveList, (msg) => {
    renderArchiveList(msg.archives);
    showArchiveBrowser(msg.storageAvailable);
  });

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

  // The imported session is selected for replay: an output like any user's selection, taken by
  // `t_subscribe` or a `t_switch_from_*` according to the session phase.
  const t_on_archive_imported = Transition.builder('t_on_archive_imported')
    .inputs(one(p.msgArchiveImported))
    .outputs(xor(
      and(outPlace(p.routerReady), outPlace(p.userSelectSession.place)),
      outPlace(p.deadLetter),
    ))
    .timing(immediate())
    .action(async (ctx) => {
      const msg = ctx.input(p.msgArchiveImported);
      try {
        hideArchiveBrowser();
      } catch (error) {
        ctx.output(p.deadLetter, { reason: 'handler-failed', message: msg, error });
        return;
      }
      ctx.output(p.routerReady, undefined);
      ctx.output(p.userSelectSession.place, { sessionId: msg.sessionId, mode: 'replay' });
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
      t_subscribe, t_switch_from_live, t_switch_from_replay_paused, t_switch_from_replay_playing,
      t_switch_from_breakpoint, t_abandon_subscribe,
      t_route_message, t_log_dead_letter,
      t_on_subscribed, t_drop_subscribed, t_on_unsubscribed, t_on_session_list, t_on_session_list_deep_link,
      t_on_event, t_drop_event, t_on_event_batch, t_on_replay_event_batch, t_drop_event_batch,
      t_on_marking_snapshot, t_drop_marking_snapshot,
      t_on_playback_state, t_on_breakpoint_hit, t_on_bp_list, t_on_bp_set,
      t_on_bp_cleared, t_on_filter_applied, t_on_error,
      t_render_dot, t_toggle_subnets,
      t_fan_out_dirty, t_frame, t_idle_frame,
      t_update_highlighting, t_skip_highlighting, t_await_diagram,
      t_update_event_log, t_skip_event_log, t_update_marking, t_skip_marking,
      t_replay_play, t_replay_play_from_bp, t_replay_auto_step, t_replay_pause, t_drop_stale_tick,
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

  const emptyFilterState: FilterState = { eventTypes: [], transitionNames: [], placeNames: [], instancePrefixes: [], excludeEventTypes: [], excludeTransitionNames: [], excludePlaceNames: [], filteredIndices: null };
  const emptySearchState: SearchState = { searchTerm: '', matches: [], currentMatchIndex: -1 };

  const initialTokens = new Map<Place<unknown>, Token<unknown>[]>([
    [p.idle, [tokenOf(undefined)]],
    [p.noSession, [tokenOf(undefined)]],
    [p.routerReady, [tokenOf(undefined)]],
    [p.modalClosed, [tokenOf(undefined)]],
    [p.breakpoints, [tokenOf([] as BreakpointConfig[])]],
    [p.filterState, [tokenOf(emptyFilterState)]],
    [p.searchState, [tokenOf(emptySearchState)]],
  ]);

  return { net, initialTokens };
}

