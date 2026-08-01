import type { Place } from './place.js';

/**
 * Arc types connecting places to transitions in the Petri net.
 *
 * | Arc Type  | Requires Token? | Consumes? | Effect                   |
 * |-----------|-----------------|-----------|--------------------------|
 * | Input     | Yes             | Yes       | Token consumed on fire   |
 * | Output    | No              | No        | Token produced on complete|
 * | Inhibitor | No (blocks)     | No        | Disables transition      |
 * | Read      | Yes             | No        | Token remains            |
 * | Reset     | No              | Yes (all) | All tokens removed       |
 */
export type Arc = ArcInput | ArcOutput | ArcInhibitor | ArcRead | ArcReset;

export interface ArcInput<T = any> {
  readonly type: 'input';
  readonly place: Place<T>;
}

export interface ArcOutput<T = any> {
  readonly type: 'output';
  readonly place: Place<T>;
}

export interface ArcInhibitor<T = any> {
  readonly type: 'inhibitor';
  readonly place: Place<T>;
}

export interface ArcRead<T = any> {
  readonly type: 'read';
  readonly place: Place<T>;
}

export interface ArcReset<T = any> {
  readonly type: 'reset';
  readonly place: Place<T>;
}

// ==================== Factory Functions ====================

/** Input arc: consumes token from place when transition fires. */
export function inputArc<T>(place: Place<T>): ArcInput<T> {
  return { type: 'input', place };
}

/** Output arc: produces token to place when transition fires. */
export function outputArc<T>(place: Place<T>): ArcOutput<T> {
  return { type: 'output', place };
}

/** Inhibitor arc: blocks transition if place has tokens. */
export function inhibitorArc<T>(place: Place<T>): ArcInhibitor<T> {
  return { type: 'inhibitor', place };
}

/** Read arc: requires token without consuming. */
export function readArc<T>(place: Place<T>): ArcRead<T> {
  return { type: 'read', place };
}

/** Reset arc: removes all tokens from place when firing. */
export function resetArc<T>(place: Place<T>): ArcReset<T> {
  return { type: 'reset', place };
}

/** Returns the place this arc connects to. */
export function arcPlace(arc: Arc): Place<any> {
  return arc.place;
}
