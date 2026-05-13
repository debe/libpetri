import type { Place } from './place.js';

/** @internal Symbol key restricting construction to {@link FusionSet.builder} and {@link FusionSet.of}. */
const FUSION_SET_KEY = Symbol('FusionSet.internal');

/**
 * A declaration that N typed places are to be treated as a single canonical
 * place in the resulting flat {@link import('./petri-net.js').PetriNet}, per
 * `spec/11-modular-composition.md` requirements **MOD-060** (fusion set
 * declaration) and **MOD-061** (fusion resolution at build).
 *
 * Fusion is **orthogonal to subnet composition**: composition merges places
 * via port-binding (one instance port place ↔ one caller place per binding);
 * fusion merges N places at once via N-ary equivalence, applied **after** all
 * `compose(...)` calls have flattened subnet instances into the enclosing
 * {@link import('./petri-net.js').PetriNetBuilder}. Fusion is the mechanism
 * for modeling shared cross-instance state — e.g., a global rate limiter
 * shared by three instances of a leaky-bucket subnet — without expressing the
 * shared resource as an interface port on every subnet.
 *
 * ## Canonical member
 *
 * The **first declared member** is the canonical place; the others are
 * non-canonical and get substituted away at
 * {@link import('./petri-net.js').PetriNetBuilder.build} time. The canonical
 * member's name and identity survive into the resulting flat net;
 * non-canonical members do not appear in the built net's place set.
 *
 * ## Token-type homogeneity (MOD-060)
 *
 * All members of a fusion set MUST share the same token type. **In
 * TypeScript** this is enforced at **compile time only** (via the typed
 * `<T>` parameter on {@link FusionSetBuilder.member} and the typed varargs of
 * {@link FusionSet.of}); per the TS-specific MOD-022 clause, no runtime
 * `tokenType` introspection exists because Place carries only a phantom
 * generic. The Java implementation enforces the same invariant at runtime.
 *
 * ## Single-member sets
 *
 * A fusion set with a single member is degenerate but allowed: it is a no-op
 * at fusion-resolution time (the canonical member maps to itself, no
 * substitution occurs). This matches the structural semantics of an N-ary
 * equivalence with N=1.
 *
 * ## Identity
 *
 * `FusionSet` is immutable after construction. The {@link members} array is
 * frozen; iteration order is the declaration order, with the first element
 * guaranteed to be the canonical member.
 *
 * @see import('./petri-net.js').PetriNetBuilder.fuse
 */
export class FusionSet {
  readonly name: string;
  readonly members: readonly Place<unknown>[];

  /** @internal Use {@link FusionSet.builder} or {@link FusionSet.of} to create instances. */
  constructor(key: symbol, name: string, members: readonly Place<unknown>[]) {
    if (key !== FUSION_SET_KEY) {
      throw new Error('Use FusionSet.builder() or FusionSet.of() to create instances');
    }
    this.name = name;
    this.members = members;
  }

  /**
   * Returns the canonical member — by convention, the first declared member.
   * The canonical place's identity survives into the resulting flat net.
   */
  get canonical(): Place<unknown> {
    return this.members[0]!;
  }

  /**
   * Returns all members **except** the canonical member, in declaration order.
   * These are the places that get substituted away at
   * {@link import('./petri-net.js').PetriNetBuilder.build} time.
   *
   * For a single-member (degenerate) set, returns an empty array.
   */
  nonCanonical(): readonly Place<unknown>[] {
    if (this.members.length <= 1) return [];
    return this.members.slice(1);
  }

  toString(): string {
    return `FusionSet[${this.name}, canonical=${this.canonical.name}, members=${this.members.length}]`;
  }

  // ============================================================
  //  Static factories
  // ============================================================

  /** Returns a fresh {@link FusionSetBuilder} with the given human-readable name. */
  static builder(name: string): FusionSetBuilder {
    return new FusionSetBuilder(name);
  }

  /**
   * Convenience factory: builds a fusion set whose first member is `first`
   * (the canonical) and whose remaining members are `rest`, all sharing the
   * type `<T>`.
   *
   * The varargs form ensures static-type homogeneity at the call site (the
   * TypeScript compiler checks every `rest` entry is a `Place<T>`).
   */
  static of<T>(name: string, first: Place<T>, ...rest: Place<T>[]): FusionSet {
    const members: Place<unknown>[] = [first as Place<unknown>];
    for (const p of rest) members.push(p as Place<unknown>);
    return new FusionSet(FUSION_SET_KEY, name, Object.freeze(members));
  }
}

/**
 * Fluent builder for {@link FusionSet}.
 *
 * Members are appended in call order; the first member becomes the canonical
 * place. The typed `<T>` parameter on {@link member} is for compile-time
 * guidance only — TypeScript erases generics at runtime, so no homogeneity
 * check happens here.
 */
export class FusionSetBuilder {
  private readonly _name: string;
  private readonly _members: Place<unknown>[] = [];

  constructor(name: string) {
    if (typeof name !== 'string' || name.length === 0) {
      throw new Error('FusionSet.builder: name must be a non-empty string');
    }
    this._name = name;
  }

  /**
   * Appends a member to the fusion set. The first member becomes the canonical
   * place per the convention documented on {@link FusionSet}.
   *
   * The `<T>` parameter is for compile-time guidance only: callers writing
   * typed code at the same call site benefit from the compiler checking
   * `Place<T>` at each member.
   */
  member<T>(place: Place<T>): this {
    if (place === undefined || place === null) {
      throw new Error(`FusionSet '${this._name}': member place must not be null`);
    }
    this._members.push(place as Place<unknown>);
    return this;
  }

  /**
   * Builds the immutable {@link FusionSet}. Validates that the set has at
   * least one member; the empty set is rejected as malformed per **MOD-060**.
   * Single-member sets are accepted as a structurally degenerate no-op.
   */
  build(): FusionSet {
    if (this._members.length === 0) {
      throw new Error(
        `FusionSet '${this._name}': must have at least one member (MOD-060)`,
      );
    }
    return new FusionSet(FUSION_SET_KEY, this._name, Object.freeze(this._members.slice()));
  }
}

/**
 * @internal Re-exported symbol key so the {@link FusionSet} test harness can
 * verify the symbol-guard. NOT part of the public API surface.
 */
export const __FUSION_SET_KEY_FOR_TEST = FUSION_SET_KEY;
