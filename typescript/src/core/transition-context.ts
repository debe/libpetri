import type { Place } from './place.js';
import type { Token } from './token.js';
import type { TokenInput } from './token-input.js';
import { TokenOutput } from './token-output.js';

/** Callback for emitting log messages from transition actions. */
export type LogFn = (level: string, message: string, error?: Error) => void;

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

  constructor(
    transitionName: string,
    rawInput: TokenInput,
    rawOutput: TokenOutput,
    inputPlaces: ReadonlySet<Place<any>>,
    readPlaces: ReadonlySet<Place<any>>,
    outputPlaces: ReadonlySet<Place<any>>,
    executionContext?: Map<string, unknown>,
    logFn?: LogFn,
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
  }

  // ==================== Input Access (consumed) ====================

  /** Get single consumed input value. Throws if place not declared or multiple tokens. */
  input<T>(place: Place<T>): T {
    this.requireInput(place);
    const values = this.rawInput.values(place);
    if (values.length !== 1) {
      throw new Error(
        `Place '${place.name}' consumed ${values.length} tokens, use inputs() for batched access`
      );
    }
    return values[0]!;
  }

  /** Get all consumed input values for a place. */
  inputs<T>(place: Place<T>): readonly T[] {
    this.requireInput(place);
    return this.rawInput.values(place);
  }

  /** Get consumed input token with metadata. */
  inputToken<T>(place: Place<T>): Token<T> {
    this.requireInput(place);
    return this.rawInput.get(place);
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
    this.requireRead(place);
    return this.rawInput.value(place);
  }

  /** Get all read-only context values for a place. */
  reads<T>(place: Place<T>): readonly T[] {
    this.requireRead(place);
    return this.rawInput.values(place);
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

  /** Add output value. Throws if place not declared as output. */
  output<T>(place: Place<T>, value: T): this {
    this.requireOutput(place);
    this._rawOutput.add(place, value);
    return this;
  }

  /** Add output token with metadata. */
  outputToken<T>(place: Place<T>, token: Token<T>): this {
    this.requireOutput(place);
    this._rawOutput.addToken(place, token);
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
