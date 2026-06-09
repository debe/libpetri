import type { Place } from './place.js';
import type { Token } from './token.js';
import type { TokenInput } from './token-input.js';
import { TokenOutput } from './token-output.js';
import { type NameId, nameId } from './name.js';

/** Callback for emitting log messages from transition actions. */
export type LogFn = (level: string, message: string, error?: Error) => void;

/** @internal Shared empty correspondence for the common (identity) case. */
const EMPTY_ALIAS: ReadonlyMap<string, Place<any>> = new Map();

/**
 * @internal Process-global fallback counter for {@link TransitionContext.freshName}
 * when no executor-installed minter is present (e.g. a context built directly in
 * a unit test). Guarantees uniqueness; the executor installs a deterministic
 * per-run minter for replay-stable names.
 */
let GLOBAL_FRESH_NAME_COUNTER = 0;

/**
 * Context provided to transition actions.
 *
 * Provides filtered access based on structure:
 * - Input places (consumed tokens)
 * - Read places (context tokens, not consumed)
 * - Output places (where to produce tokens)
 *
 * Enforces the structure contract — actions can only access places
 * declared in the transition's structure.
 */
export class TransitionContext {
  private readonly rawInput: TokenInput;
  private readonly _rawOutput: TokenOutput;
  private readonly allowedInputs: Set<string>;
  private readonly allowedReads: Set<string>;
  private readonly allowedOutputs: Set<string>;
  private readonly _inputPlaces: ReadonlySet<Place<any>>;
  private readonly _readPlaces: ReadonlySet<Place<any>>;
  private readonly _outputPlaces: ReadonlySet<Place<any>>;
  private readonly _transitionName: string;
  private readonly executionCtx: Map<string, unknown>;
  private readonly _logFn?: LogFn;
  private readonly placeAlias: ReadonlyMap<string, Place<any>>;
  private _freshNameSupplier?: () => NameId;

  constructor(
    transitionName: string,
    rawInput: TokenInput,
    rawOutput: TokenOutput,
    inputPlaces: ReadonlySet<Place<any>>,
    readPlaces: ReadonlySet<Place<any>>,
    outputPlaces: ReadonlySet<Place<any>>,
    executionContext?: Map<string, unknown>,
    logFn?: LogFn,
    placeAlias?: ReadonlyMap<string, Place<any>>,
  ) {
    this._transitionName = transitionName;
    this.rawInput = rawInput;
    this._rawOutput = rawOutput;
    this._inputPlaces = inputPlaces;
    this._readPlaces = readPlaces;
    this._outputPlaces = outputPlaces;
    const ai = new Set<string>();
    for (const p of inputPlaces) ai.add(p.name);
    this.allowedInputs = ai;
    const ar = new Set<string>();
    for (const p of readPlaces) ar.add(p.name);
    this.allowedReads = ar;
    const ao = new Set<string>();
    for (const p of outputPlaces) ao.add(p.name);
    this.allowedOutputs = ao;
    this.executionCtx = executionContext ?? new Map();
    this._logFn = logFn;
    this.placeAlias = placeAlias ?? EMPTY_ALIAS;
  }

  /**
   * Resolves a place key through the transition's declared→actual place
   * correspondence (per **MOD-031**). For a hand-written or directly-composed
   * transition the correspondence is the identity, so this returns `place`
   * unchanged; after instancing / port binding it maps a *declared* place
   * constant the action hardcodes to the *actual* composed place. The result
   * feeds both the declared-set check and the token-store access (both keyed by
   * `place.name`), so `inputPlaces()`/`outputPlaces()` discovery is unaffected.
   */
  private resolve<T>(place: Place<T>): Place<T> {
    const actual = this.placeAlias.get(place.name);
    return actual !== undefined ? (actual as Place<T>) : place;
  }

  // ==================== Input Access (consumed) ====================

  /** Get single consumed input value. Throws if place not declared or multiple tokens. */
  input<T>(place: Place<T>): T {
    const actual = this.resolve(place);
    this.requireInput(actual);
    const values = this.rawInput.values(actual);
    if (values.length !== 1) {
      throw new Error(
        `Place '${actual.name}' consumed ${values.length} tokens, use inputs() for batched access`
      );
    }
    return values[0]!;
  }

  /** Get all consumed input values for a place. */
  inputs<T>(place: Place<T>): readonly T[] {
    const actual = this.resolve(place);
    this.requireInput(actual);
    return this.rawInput.values(actual);
  }

  /** Get consumed input token with metadata. */
  inputToken<T>(place: Place<T>): Token<T> {
    const actual = this.resolve(place);
    this.requireInput(actual);
    return this.rawInput.get(actual);
  }

  /** Returns declared input places (consumed). */
  inputPlaces(): ReadonlySet<Place<any>> {
    return this._inputPlaces;
  }

  private requireInput(place: Place<any>): void {
    if (!this.allowedInputs.has(place.name)) {
      throw new Error(
        `Place '${place.name}' not in declared inputs: [${[...this.allowedInputs].join(', ')}]`
      );
    }
  }

  // ==================== Read Access (not consumed) ====================

  /** Get read-only context value. Throws if place not declared as read. */
  read<T>(place: Place<T>): T {
    const actual = this.resolve(place);
    this.requireRead(actual);
    return this.rawInput.value(actual);
  }

  /** Get all read-only context values for a place. */
  reads<T>(place: Place<T>): readonly T[] {
    const actual = this.resolve(place);
    this.requireRead(actual);
    return this.rawInput.values(actual);
  }

  /** Returns declared read places (context, not consumed). */
  readPlaces(): ReadonlySet<Place<any>> {
    return this._readPlaces;
  }

  private requireRead(place: Place<any>): void {
    if (!this.allowedReads.has(place.name)) {
      throw new Error(
        `Place '${place.name}' not in declared reads: [${[...this.allowedReads].join(', ')}]`
      );
    }
  }

  // ==================== Output Access ====================

  /**
   * Add one or more output values to the same place in a single call.
   *
   * Validates the place once, then appends each value to the output
   * collector. Calling with zero values is a no-op.
   *
   * @example
   *   ctx.output(outPlace, 'a', 'b', 'c');
   *   ctx.output(outPlace, ...someArray);
   *
   * @throws if place not declared as output.
   */
  output<T>(place: Place<T>, ...values: T[]): this {
    const actual = this.resolve(place);
    this.requireOutput(actual);
    for (const value of values) {
      this._rawOutput.add(actual, value);
    }
    return this;
  }

  /**
   * Add one or more pre-built output tokens to the same place in a single call.
   *
   * Validates the place once, then appends each token. Calling with zero
   * tokens is a no-op.
   *
   * @throws if place not declared as output.
   */
  outputToken<T>(place: Place<T>, ...tokens: Token<T>[]): this {
    const actual = this.resolve(place);
    this.requireOutput(actual);
    for (const token of tokens) {
      this._rawOutput.addToken(actual, token);
    }
    return this;
  }

  /** Returns declared output places. */
  outputPlaces(): ReadonlySet<Place<any>> {
    return this._outputPlaces;
  }

  private requireOutput(place: Place<any>): void {
    if (!this.allowedOutputs.has(place.name)) {
      throw new Error(
        `Place '${place.name}' not in declared outputs: [${[...this.allowedOutputs].join(', ')}]`
      );
    }
  }

  // ==================== ν-name minting (NU-010) ====================

  /**
   * @internal Installs the ν-name minter. Wired by the executor at firing time
   * so names minted by {@link freshName} are monotonic across the run and
   * instance-prefixed (spec NU-010, NU-030).
   */
  setFreshNameSupplier(supplier: () => NameId): void {
    this._freshNameSupplier = supplier;
  }

  /**
   * Mints a fresh ν-name (the ν-binder primitive — spec NU-010).
   *
   * An action calls this on the fork side to create a correlation id, then
   * writes it into the sibling output payloads; a later join correlates those
   * siblings via a {@link import('./match-spec.js').MatchSpec}. Uses the
   * executor-installed minter when present; otherwise falls back to a
   * process-global counter prefixed by the transition name.
   */
  freshName(): NameId {
    if (this._freshNameSupplier) return this._freshNameSupplier();
    return nameId(`${this._transitionName}#${GLOBAL_FRESH_NAME_COUNTER++}`);
  }

  // ==================== Structure Info ====================

  /** Returns the transition name. */
  transitionName(): string {
    return this._transitionName;
  }

  // ==================== Execution Context ====================

  /** Retrieves an execution context object by key. */
  executionContext<T>(key: string): T | undefined {
    return this.executionCtx.get(key) as T | undefined;
  }

  /** Checks if an execution context object of the given key is present. */
  hasExecutionContext(key: string): boolean {
    return this.executionCtx.has(key);
  }

  // ==================== Logging ====================

  /** Emits a structured log message into the event store. */
  log(level: string, message: string, error?: Error): void {
    this._logFn?.(level, message, error);
  }

  // ==================== Internal ====================

  /** @internal Used by BitmapNetExecutor to collect outputs after action completion. */
  rawOutput(): TokenOutput {
    return this._rawOutput;
  }
}
