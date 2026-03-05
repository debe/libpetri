import type { Transition } from '../../core/transition.js';
import type { MarkingState } from '../marking-state.js';
import type { DBM } from './dbm.js';

/**
 * A State Class in Time Petri Net analysis.
 *
 * A state class is a pair (M, D) where M is a marking and D is a firing domain (DBM).
 * State classes provide a finite abstraction of the infinite state space of Time Petri Nets.
 */
export class StateClass {
  readonly marking: MarkingState;
  readonly firingDomain: DBM;
  readonly enabledTransitions: readonly Transition[];

  constructor(marking: MarkingState, firingDomain: DBM, enabledTransitions: readonly Transition[]) {
    this.marking = marking;
    this.firingDomain = firingDomain;
    this.enabledTransitions = [...enabledTransitions];
  }

  isEmpty(): boolean {
    return this.firingDomain.isEmpty();
  }

  canFire(transition: Transition): boolean {
    const idx = this.enabledTransitions.indexOf(transition);
    if (idx < 0) return false;
    return this.firingDomain.getUpperBound(idx) >= 0;
  }

  transitionIndex(transition: Transition): number {
    return this.enabledTransitions.indexOf(transition);
  }

  equals(other: StateClass): boolean {
    if (this === other) return true;
    return this.marking.toString() === other.marking.toString()
      && this.firingDomain.equals(other.firingDomain);
  }

  toString(): string {
    return `StateClass{${this.marking}, ${this.firingDomain}}`;
  }
}
