/**
 * Shared types for the debug UI Petri net.
 */

import type { TokenInfo, NetEventInfo, NetStructure } from '../protocol/index.js';

/** Central UI state carried by the uiState resource place. */
export interface UIState {
  readonly marking: Record<string, readonly TokenInfo[]>;
  readonly enabledTransitions: readonly string[];
  readonly inFlightTransitions: readonly string[];
  readonly events: readonly NetEventInfo[];
  readonly eventIndex: number;
  readonly totalEvents: number;
}

/** Data associated with an active session subscription. */
export interface SessionData {
  readonly sessionId: string;
  readonly netName: string;
  readonly dotDiagram: string;
  readonly structure: NetStructure;
  readonly mode: 'live' | 'replay';
  /** graphId → {name, isTransition, ...} lookup */
  readonly byGraphId: Record<string, StructureLookup>;
}

export interface StructureLookup {
  readonly name: string;
  readonly isTransition: boolean;
  readonly tokenType?: string;
  readonly isStart?: boolean;
  readonly isEnd?: boolean;
}

/** State for event log filtering. */
export interface FilterState {
  readonly eventTypes: readonly string[];
  readonly transitionNames: readonly string[];
  readonly placeNames: readonly string[];
  readonly excludeEventTypes: readonly string[];
  readonly excludeTransitionNames: readonly string[];
  readonly excludePlaceNames: readonly string[];
  /** Precomputed filtered indices into UIState.events, null = no filter active */
  readonly filteredIndices: readonly number[] | null;
}

/** State for event search. */
export interface SearchState {
  readonly searchTerm: string;
  readonly matches: readonly number[];
  readonly currentMatchIndex: number;
}

/** Content for the value modal. */
export interface ModalContent {
  readonly title: string;
  readonly subtitle: string;
  readonly json: string;
}

/** Cached SVG node references for O(1) highlighting. */
export interface SvgNodeCache {
  readonly nodesByName: Map<string, Element>;
  readonly nodesByGraphId: Map<string, Element>;
  readonly edgesByGraphId: Map<string, Element[]>;
  readonly allNodeShapes: Element[];
  readonly allEdgePaths: Element[];
}

/** Checkpoint for efficient replay seeking. */
export interface Checkpoint {
  readonly index: number;
  readonly marking: Record<string, readonly TokenInfo[]>;
  readonly enabledTransitions: readonly string[];
  readonly inFlightTransitions: readonly string[];
}

/** All replay events plus checkpoint state. */
export interface ReplayData {
  readonly allEvents: NetEventInfo[];
  readonly checkpoints: Checkpoint[];
  readonly checkpointInterval: number;
}

/** Playback timer state. */
export interface PlaybackTimerState {
  readonly timer: ReturnType<typeof setTimeout> | null;
  readonly animationFrame: number | null;
  readonly speed: number;
}

/** Configuration constants. */
export const CONFIG = {
  wsReconnectDelay: 2000,
  maxPlaybackDelay: 2000,
  minPlaybackDelay: 10,
  sliderResolution: 10000,
  checkpointInterval: 20,
  maxBatchSize: 10,
  virtualLogItemHeight: 72,
  virtualLogOverscan: 10,
} as const;
