import type { Place } from './place.js';
import type { ArcInhibitor, ArcRead, ArcReset } from './arc.js';
import type { In } from './in.js';
import type { MatchSpec } from './match-spec.js';
import type { Out, OutTimeout } from './out.js';
import type { Timing } from './timing.js';
import type { TransitionAction } from './transition-action.js';
import { passthrough } from './transition-action.js';
import { immediate } from './timing.js';
import { allPlaces } from './out.js';

/** @internal Symbol key restricting construction to the builder. */
const TRANSITION_KEY = Symbol('Transition.internal');

/** @internal Shared empty correspondence for the common (identity) case. */
const EMPTY_PLACE_ALIAS: ReadonlyMap<string, Place<any>> = new Map();

/**
 * A transition in the Time Petri Net that transforms tokens.
 *
 * Transitions use identity-based equality (===) — each instance is unique
 * regardless of name. The name is purely a label for display/debugging/export.
 */
export class Transition {
  readonly name: string;
  readonly inputSpecs: readonly In[];
  readonly outputSpec: Out | null;
  readonly inhibitors: readonly ArcInhibitor[];
  readonly reads: readonly ArcRead[];
  readonly resets: readonly ArcReset[];
  readonly timing: Timing;
  readonly actionTimeout: OutTimeout | null;
  readonly action: TransitionAction;
  readonly priority: number;

  /**
   * ν-net join correlation: a subset of `inputSpecs` that must be correlated by
   * name equality on firing (spec NU-020). `null` for ordinary transitions.
   */
  readonly matchSpec: MatchSpec | null;

  /**
   * Per-transition **declared → actual** place correspondence (per
   * **MOD-031**), keyed by the author-original declared place **name** →
   * actual composed place. Empty for a hand-written or directly-composed
   * ([MOD-025]) transition (identity). Populated by the subnet rewriter after
   * instantiation ([MOD-010]) / port binding ([MOD-020]) so an action that
   * hardcodes a declared place constant resolves to the composed place via
   * {@link import('./transition-context.js').TransitionContext}. Consumed only
   * by the action-facing context I/O — never by enablement, firing, the
   * verifier, the exporter, or events (so [MOD-023] is unaffected).
   */
  readonly placeAlias: ReadonlyMap<string, Place<any>>;

  private readonly _inputPlaces: ReadonlySet<Place<any>>;
  private readonly _readPlaces: ReadonlySet<Place<any>>;
  private readonly _outputPlaces: ReadonlySet<Place<any>>;

  /** @internal Use {@link Transition.builder} to create instances. */
  constructor(
    key: symbol,
    name: string,
    inputSpecs: readonly In[],
    outputSpec: Out | null,
    inhibitors: readonly ArcInhibitor[],
    reads: readonly ArcRead[],
    resets: readonly ArcReset[],
    timing: Timing,
    action: TransitionAction,
    priority: number,
    placeAlias: ReadonlyMap<string, Place<any>> = EMPTY_PLACE_ALIAS,
    matchSpec: MatchSpec | null = null,
  ) {
    if (key !== TRANSITION_KEY) throw new Error('Use Transition.builder() to create instances');
    this.name = name;
    this.inputSpecs = inputSpecs;
    this.outputSpec = outputSpec;
    this.inhibitors = inhibitors;
    this.reads = reads;
    this.resets = resets;
    this.timing = timing;
    this.actionTimeout = findTimeout(outputSpec);
    this.action = action;
    this.priority = priority;
    this.placeAlias = placeAlias.size === 0 ? EMPTY_PLACE_ALIAS : placeAlias;
    this.matchSpec = matchSpec;

    // Precompute place sets
    const inputPlaces = new Set<Place<any>>();
    for (const spec of inputSpecs) {
      inputPlaces.add(spec.place);
    }
    this._inputPlaces = inputPlaces;

    const readPlaces = new Set<Place<any>>();
    for (const r of reads) {
      readPlaces.add(r.place);
    }
    this._readPlaces = readPlaces;

    const outputPlaces = new Set<Place<any>>();
    if (outputSpec !== null) {
      for (const p of allPlaces(outputSpec)) {
        outputPlaces.add(p);
      }
    }
    this._outputPlaces = outputPlaces;
  }

  /** Returns set of input places — consumed tokens. */
  inputPlaces(): ReadonlySet<Place<any>> {
    return this._inputPlaces;
  }

  /** Returns set of read places — context tokens, not consumed. */
  readPlaces(): ReadonlySet<Place<any>> {
    return this._readPlaces;
  }

  /** Returns set of output places — where tokens are produced. */
  outputPlaces(): ReadonlySet<Place<any>> {
    return this._outputPlaces;
  }

  /** Returns true if this transition has an action timeout. */
  hasActionTimeout(): boolean {
    return this.actionTimeout !== null;
  }

  toString(): string {
    return `Transition[${this.name}]`;
  }

  static builder(name: string): TransitionBuilder {
    return new TransitionBuilder(name);
  }
}

export class TransitionBuilder {
  private readonly _name: string;
  private readonly _inputSpecs: In[] = [];
  private _outputSpec: Out | null = null;
  private readonly _inhibitors: ArcInhibitor[] = [];
  private readonly _reads: ArcRead[] = [];
  private readonly _resets: ArcReset[] = [];
  private _timing: Timing = immediate();
  private _action: TransitionAction = passthrough();
  private _priority = 0;
  private _placeAlias: ReadonlyMap<string, Place<any>> = EMPTY_PLACE_ALIAS;
  private _matchSpec: MatchSpec | null = null;

  constructor(name: string) {
    this._name = name;
  }

  /** Add input specifications with cardinality. */
  inputs(...specs: In[]): this {
    this._inputSpecs.push(...specs);
    return this;
  }

  /** Set the output specification (composite AND/XOR structure). */
  outputs(spec: Out): this {
    this._outputSpec = spec;
    return this;
  }

  /** Add inhibitor arc. */
  inhibitor(place: Place<any>): this {
    this._inhibitors.push({ type: 'inhibitor', place });
    return this;
  }

  /** Add inhibitor arcs. */
  inhibitors(...places: Place<any>[]): this {
    for (const p of places) {
      this._inhibitors.push({ type: 'inhibitor', place: p });
    }
    return this;
  }

  /** Add read arc. */
  read(place: Place<any>): this {
    this._reads.push({ type: 'read', place });
    return this;
  }

  /** Add read arcs. */
  reads(...places: Place<any>[]): this {
    for (const p of places) {
      this._reads.push({ type: 'read', place: p });
    }
    return this;
  }

  /** Add reset arc. */
  reset(place: Place<any>): this {
    this._resets.push({ type: 'reset', place });
    return this;
  }

  /** Add reset arcs. */
  resets(...places: Place<any>[]): this {
    for (const p of places) {
      this._resets.push({ type: 'reset', place: p });
    }
    return this;
  }

  /** Set timing specification. */
  timing(timing: Timing): this {
    this._timing = timing;
    return this;
  }

  /** Set the transition action. */
  action(action: TransitionAction): this {
    this._action = action;
    return this;
  }

  /** Set the priority (higher fires first). */
  priority(priority: number): this {
    this._priority = priority;
    return this;
  }

  /**
   * Sets the ν-net join correlation spec: the named input places must be
   * correlated by name equality on firing (spec NU-020). Every place referenced
   * by the spec must also be declared as an input.
   */
  match(spec: MatchSpec): this {
    this._matchSpec = spec;
    return this;
  }

  /**
   * Sets the per-transition declared→actual place correspondence (per
   * **MOD-031**). Populated by the subnet rewriter during the compose-time
   * rewrite; not normally called by hand-written nets, whose correspondence is
   * the identity (empty map).
   */
  placeAlias(alias: ReadonlyMap<string, Place<any>>): this {
    this._placeAlias = alias;
    return this;
  }

  build(): Transition {
    // Validate ForwardInput references
    if (this._outputSpec !== null) {
      const inputPlaceNames = new Set(this._inputSpecs.map(s => s.place.name));
      for (const fi of findForwardInputs(this._outputSpec)) {
        if (!inputPlaceNames.has(fi.from.name)) {
          throw new Error(
            `Transition '${this._name}': ForwardInput references non-input place '${fi.from.name}'`
          );
        }
      }
    }

    // Validate MatchSpec correlates only declared input places (NU-020).
    if (this._matchSpec !== null) {
      const inputPlaceNames = new Set(this._inputSpecs.map(s => s.place.name));
      for (const k of this._matchSpec.keys) {
        if (!inputPlaceNames.has(k.place.name)) {
          throw new Error(
            `Transition '${this._name}': MatchSpec correlates non-input place '${k.place.name}'`
          );
        }
      }
    }

    return new Transition(
      TRANSITION_KEY,
      this._name,
      [...this._inputSpecs],
      this._outputSpec,
      [...this._inhibitors],
      [...this._reads],
      [...this._resets],
      this._timing,
      this._action,
      this._priority,
      this._placeAlias,
      this._matchSpec,
    );
  }
}

/** Recursively searches the output spec for a Timeout node. */
function findTimeout(out: Out | null): OutTimeout | null {
  if (out === null) return null;
  switch (out.type) {
    case 'timeout': return out;
    case 'and':
    case 'xor':
      for (const child of out.children) {
        const found = findTimeout(child);
        if (found !== null) return found;
      }
      return null;
    case 'place':
    case 'forward-input':
      return null;
  }
}

/** Recursively finds all ForwardInput nodes in the output spec. */
function findForwardInputs(out: Out): Array<{ from: Place<any>; to: Place<any> }> {
  switch (out.type) {
    case 'forward-input':
      return [{ from: out.from, to: out.to }];
    case 'and':
    case 'xor':
      return out.children.flatMap(findForwardInputs);
    case 'timeout':
      return findForwardInputs(out.child);
    case 'place':
      return [];
  }
}
