/**
 * Event capture system for Petri net execution.
 *
 * Defines the `NetEvent` discriminated union (execution lifecycle, transition lifecycle,
 * token flow, log messages) and `EventStore` interface. Use `InMemoryEventStore` for
 * debugging/testing, or `noopEventStore()` for production (zero overhead).
 *
 * @module event
 */
export type {
  NetEvent,
  ExecutionStarted, ExecutionCompleted,
  TransitionEnabled, TransitionClockRestarted,
  TransitionStarted, TransitionCompleted, TransitionFailed,
  TransitionTimedOut, ActionTimedOut,
  TokenAdded, TokenRemoved,
  LogMessage, MarkingSnapshot,
} from './net-event.js';
export { eventTransitionName, isFailureEvent } from './net-event.js';

export type { EventStore } from './event-store.js';
export {
  InMemoryEventStore, noopEventStore, inMemoryEventStore,
  filterEvents, eventsOfType, transitionEvents, failures,
} from './event-store.js';
