import type { StateClass } from './state-class.js';
import type { NameMarking } from './name-marking.js';

/**
 * A name-aware state class (NU-050, Route B): the base count + DBM
 * {@link StateClass} plus the abstract {@link NameMarking} partition layer. The
 * base class is reused verbatim, so the timing/zone dimension is untouched —
 * name×time composition is automatic. The dedup `key` is the base key
 * (marking + DBM zone) joined with the symmetry-canonical name-partition key.
 */
export class NameStateClass {
  readonly base: StateClass;
  readonly names: NameMarking;
  readonly key: string;

  constructor(base: StateClass, names: NameMarking, colouredOrder: readonly string[]) {
    this.base = base;
    this.names = names;
    this.key = `${base.marking.toString()}|${base.firingDomain.toString()}||${names.canonicalKey(colouredOrder)}`;
  }
}
