import type { Place } from './place.js';
import type { ArcInhibitor, ArcRead, ArcReset } from './arc.js';
import type { In } from './in.js';
import type { Out, OutTimeout } from './out.js';
import type { Timing } from './timing.js';
import type { TransitionAction } from './transition-action.js';
import { passthrough } from './transition-action.js';
import { immediate } from './timing.js';
import { allPlaces } from './out.js';

/** @internal Symbol key restricting construction to the builder. */
const TRANSITION_KEY = Symbol('Transition.internal');

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
