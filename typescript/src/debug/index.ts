/**
 * Debug infrastructure for Petri net execution visualization.
 *
 * Provides a framework-agnostic debug protocol handler, event store with
 * live tailing, session registry, and marking cache for efficient replay.
 *
 * @module debug
 */

// Protocol types
export type { DebugCommand, SubscriptionMode, BreakpointType, BreakpointConfig, EventFilter } from './debug-command.js';
export { eventFilterAll } from './debug-command.js';
export type {
  DebugResponse, SessionSummary, TokenInfo, NetEventInfo,
  PlaceInfo, TransitionInfo, NetStructure,
} from './debug-response.js';

// Core infrastructure
export { DebugProtocolHandler } from './debug-protocol-handler.js';
export type { ResponseSink, ComputedState } from './debug-protocol-handler.js';
export { DebugEventStore, DEFAULT_MAX_EVENTS } from './debug-event-store.js';
export type { Subscription } from './debug-event-store.js';
export { DebugSessionRegistry } from './debug-session-registry.js';
export type { DebugSession, EventStoreFactory } from './debug-session-registry.js';
export { MarkingCache, SNAPSHOT_INTERVAL } from './marking-cache.js';

// Converters and analysis
export { toEventInfo, tokenInfo, compactTokenInfo, convertMarking } from './net-event-converter.js';
export { DebugAwareEventStore } from './debug-aware-event-store.js';
export { PlaceAnalysis } from './place-analysis.js';
export type { PlaceAnalysisInfo } from './place-analysis.js';

/**
 * Returns the path to the bundled debug UI assets directory.
 * Requires Node.js — resolves relative to this module's location.
 */
export async function debugUiAssetPath(): Promise<string> {
  // eslint-disable-next-line @typescript-eslint/no-implied-eval
  const dynamicImport = Function('m', 'return import(m)') as (m: string) => Promise<Record<string, unknown>>;
  const nodeUrl = await dynamicImport('node:url') as { fileURLToPath(url: string | URL): string };
  const nodePath = await dynamicImport('node:path') as { dirname(p: string): string; join(...paths: string[]): string };
  const thisDir = nodePath.dirname(nodeUrl.fileURLToPath(import.meta.url));
  return nodePath.join(thisDir, '..', 'debug-ui');
}
