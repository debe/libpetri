import type { StateClass } from './state-class.js';
import type { NameMarking } from './name-marking.js';

/**
 * A name-aware state class (NU-050, Route B): the base count + DBM
 * {@link StateClass} plus the abstract {@link NameMarking} partition layer. The
 * base class is reused verbatim, so the timing/zone dimension is untouched —
 * name×time composition is automatic.
 *
 * Both layers are interned by {@link NameStateClassGraph.build} (VER-012): a class
 * shares its base with every class at the same marking, zone and earliest-ready
 * times, and its name layer with every class whose partition has the same
 * canonical key — a renaming of it, which every consumer of the layer is
 * invariant under (`Interning.lean`, `interned_keys_eq`).
 */
export class NameStateClass {
  readonly base: StateClass;
  readonly names: NameMarking;
  /** The symmetry-canonical name-partition key (the name layer's intern key). */
  readonly nameKey: string;

  constructor(base: StateClass, names: NameMarking, colouredOrder: readonly string[], nameKey?: string) {
    this.base = base;
    this.names = names;
    this.nameKey = nameKey ?? names.canonicalKey(colouredOrder);
  }

  /** Full dedup key: the base key (marking + DBM zone) joined with the name key. */
  get key(): string {
    return `${baseKeyOf(this.base)}||${this.nameKey}`;
  }
}

/** The base layer's identity for dedup: marking + DBM zone (what `StateClass.equals` compares). */
export function baseKeyOf(base: StateClass): string {
  return `${base.marking.toString()}|${base.firingDomain.toString()}`;
}
