/**
 * Mutable shared state accessible to transition actions.
 *
 * The CTPN controls flow (which transitions fire when), but actions need
 * mutable state for WebSocket, DOM caches, replay data, etc.
 */

import type { SvgNodeCache, Checkpoint, SessionData } from './types.js';
import type { DebugCommand, NetEventInfo } from '../protocol/index.js';

/** Mutable versions of readonly types for shared state. */
interface MutableReplayData {
  allEvents: NetEventInfo[];
  checkpoints: Checkpoint[];
  checkpointInterval: number;
}

interface MutablePlaybackTimerState {
  timer: ReturnType<typeof setTimeout> | null;
  animationFrame: number | null;
  speed: number;
}

/** Mutable shared state. */
export const shared = {
  ws: null as WebSocket | null,
  panzoomInstance: null as ReturnType<typeof import('panzoom')['default']> | null,
  svgNodeCache: null as SvgNodeCache | null,
  prevHighlighted: { shapes: [] as Element[], edges: [] as Element[] },
  replay: {
    allEvents: [],
    checkpoints: [],
    checkpointInterval: 20,
  } as MutableReplayData,
  playback: {
    timer: null,
    animationFrame: null,
    speed: 1.0,
  } as MutablePlaybackTimerState,
  /** Virtual scroll state */
  virtualLog: {
    itemHeight: 72,
    overscan: 10,
    followMode: true,
  },
  /** Pending slider seek (rAF-throttled) */
  pendingSeekIndex: null as number | null,
  seekRafId: null as number | null,
  /** Current session data (set on subscribe, cleared on disconnect). */
  currentSession: null as SessionData | null,
  /** Current subscription mode. */
  currentMode: null as 'live' | 'replay' | null,
};

/** Send a command over the WebSocket. */
export function sendCommand(command: DebugCommand): void {
  if (shared.ws && shared.ws.readyState === WebSocket.OPEN) {
    shared.ws.send(JSON.stringify(command));
  }
}
