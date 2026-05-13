import type { Place } from './place.js';
import type { Transition } from './transition.js';

/**
 * @internal Symbol key restricting construction to
 * {@link PetriNetBuilder.compose}. Bindings are produced by the host builder
 * and supplied to the caller's callback — direct construction is not part of
 * the public API.
 */
const COMPOSE_BINDINGS_KEY = Symbol('ComposeBindings.internal');

/**
 * Typed binding builder for {@link PetriNetBuilder.compose}, per
 * `spec/11-modular-composition.md` requirements **MOD-020** (composition
 * operation) and **MOD-022** (type compatibility).
 *
 * `ComposeBindings` is a write-only collector: callers register port and
 * channel bindings against an instance's interface, and the host builder
 * consumes the recorded mappings as it merges the instance into the
 * enclosing net.
 *
 * ## Port bindings (MOD-020, MOD-022)
 *
 * {@link bindPort} merges an interface port with a caller-side place. The
 * port name is the **original** (pre-prefix) name declared in the subnet's
 * `Interface`; the caller place takes the port's slot in the resulting net.
 * Token-type compatibility is enforced at compile time only in TypeScript
 * (per [MOD-022]) — the typed `bindPort<T>` signature is the safety
 * mechanism. TypeScript erases generics at runtime, so a misuse via `as`
 * casts is structurally undetectable.
 *
 * ## Channel bindings (MOD-021)
 *
 * {@link bindChannel} records a synchronous channel binding: at compose time
 * the named instance-side interface transition is **merged** with the
 * supplied caller-side {@link Transition} into one transition in the
 * resulting flat net. Channel composition is implemented in task #13; until
 * then `compose(...)` raises an `Error` when any channel binding is present.
 *
 * ## Identity
 *
 * Instances are produced by {@link PetriNetBuilder.compose} and supplied to
 * the caller's callback. The constructor is symbol-guarded to prevent
 * direct construction.
 */
export class ComposeBindings {
  private readonly _portBindings = new Map<string, Place<unknown>>();
  private readonly _channelBindings = new Map<string, Transition>();

  /**
   * @internal Use {@link PetriNetBuilder.compose} — instances are produced
   * by the host builder and supplied to the caller's callback.
   */
  constructor(key: symbol) {
    if (key !== COMPOSE_BINDINGS_KEY) {
      throw new Error(
        'Use PetriNetBuilder.compose(instance, b => ...) — ComposeBindings is not directly constructible',
      );
    }
  }

  /**
   * Binds the named interface port to the given caller place per **MOD-020**.
   *
   * The port name is the **original** (pre-prefix) name declared in the
   * subnet's `Interface`. The typed `<T>` parameter ensures the caller
   * place's token type matches the interface port's token type at compile
   * time per [MOD-022]; TypeScript does not validate the type at runtime
   * because generics are erased.
   *
   * @throws when `portName` is already bound on this builder
   */
  bindPort<T>(portName: string, callerPlace: Place<T>): this {
    if (this._portBindings.has(portName)) {
      throw new Error(`Port '${portName}' is already bound`);
    }
    this._portBindings.set(portName, callerPlace as Place<unknown>);
    return this;
  }

  /**
   * Records a synchronous channel binding per **MOD-021**: at compose time,
   * the instance-side renamed channel transition is merged with
   * `callerTransition` into a single transition in the resulting flat net.
   *
   * **Status**: channel composition is implemented in task #13. Recording a
   * channel binding here is permitted, but `compose(...)` currently raises
   * an `Error` when any channel binding is present.
   *
   * @throws when `channelName` is already bound on this builder
   */
  bindChannel(channelName: string, callerTransition: Transition): this {
    if (this._channelBindings.has(channelName)) {
      throw new Error(`Channel '${channelName}' is already bound`);
    }
    this._channelBindings.set(channelName, callerTransition);
    return this;
  }

  /** Returns an unmodifiable view of the recorded port bindings. */
  portBindings(): ReadonlyMap<string, Place<unknown>> {
    return this._portBindings;
  }

  /** Returns an unmodifiable view of the recorded channel bindings. */
  channelBindings(): ReadonlyMap<string, Transition> {
    return this._channelBindings;
  }
}

/**
 * @internal Package-internal factory used by {@link PetriNetBuilder.compose}
 * to construct {@link ComposeBindings} values without re-exporting the
 * Symbol-guarded constructor key publicly.
 *
 * NOT part of the public API surface — do NOT re-export from `core/index.ts`.
 */
export function __createComposeBindings(): ComposeBindings {
  return new ComposeBindings(COMPOSE_BINDINGS_KEY);
}
