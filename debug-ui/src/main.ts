/**
 * Debug UI entry point.
 *
 * Builds the debug UI Petri net, creates a BitmapNetExecutor,
 * wires DOM events to environment places, and starts execution.
 */

import './styles.css';
import { BitmapNetExecutor } from 'libpetri';
import { initElements } from './dom/elements.js';
import { bindDomEvents } from './dom/bindings.js';
import { startRafLoop } from './dom/raf-loop.js';
import { buildDebugNet, setExecutor } from './net/definition.js';
import { allEnvironmentPlaces } from './net/places.js';
import { shared } from './net/shared-state.js';

document.addEventListener('DOMContentLoaded', async () => {
  // Initialize cached DOM references
  initElements();

  // Build the Petri net
  const { net, initialTokens } = buildDebugNet();

  // Create executor
  const executor = new BitmapNetExecutor(net, initialTokens, {
    environmentPlaces: allEnvironmentPlaces,
  });

  // Store executor reference for transition actions
  setExecutor(executor);

  // Wire DOM events → environment place injections
  bindDomEvents(executor);

  // Parse URL for deep-linking
  const targetSessionId = new URLSearchParams(window.location.search).get('sessionId');
  if (targetSessionId) {
    shared.pendingDeepLink = targetSessionId;
  }

  // Start rAF loop for throttled UI updates
  startRafLoop(executor);

  // Run the net (never resolves in normal operation — long-running UI)
  await executor.run();
});
