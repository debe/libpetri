/**
 * Connection transition actions: WebSocket create, status updates, reconnection.
 */

import type { BitmapNetExecutor } from 'libpetri';
import { shared } from '../shared-state.js';
import * as p from '../places.js';
import type { DebugResponse } from '../../protocol/index.js';
import { el } from '../../dom/elements.js';

/** Create WebSocket and wire events to environment places. */
export function createWebSocket(executor: BitmapNetExecutor): void {
  const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
  const wsUrl = `${protocol}//${window.location.host}/debug/petri`;

  const ws = new WebSocket(wsUrl);
  shared.ws = ws;

  ws.onopen = () => {
    executor.injectValue(p.wsOpenSignal, undefined);
  };

  ws.onclose = () => {
    executor.injectValue(p.wsCloseSignal, undefined);
  };

  ws.onerror = (error) => {
    console.error('WebSocket error:', error);
  };

  ws.onmessage = (event) => {
    try {
      const response: DebugResponse = JSON.parse(event.data as string);
      executor.injectValue(p.wsMessage, response);
    } catch (e) {
      console.error('Failed to parse WebSocket message:', e);
    }
  };
}

/** Update connection status indicator to connected. */
export function setConnected(): void {
  el.statusDot.className = 'w-2 h-2 rounded-full bg-green-500';
  el.statusText.textContent = 'Connected';
}

/** Update connection status indicator to disconnected. */
export function setDisconnected(): void {
  el.statusDot.className = 'w-2 h-2 rounded-full bg-red-500';
  el.statusText.textContent = 'Disconnected';
  shared.ws = null;
}

/** Update connection status indicator to connecting. */
export function setConnecting(): void {
  el.statusDot.className = 'w-2 h-2 rounded-full bg-yellow-500';
  el.statusText.textContent = 'Connecting...';
}
