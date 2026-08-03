/**
 * Core Petri net definitions: places, transitions, arcs, tokens, timing, and actions.
 *
 * Provides the immutable structural model — build nets with `PetriNet.builder()` and
 * `Transition.builder()`, define timing with `delayed()` / `window()` / `exact()`,
 * and compose output routing with `and()` / `xor()` / `timeout()`.
 *
 * @module core
 */
export type { Token } from './token.js';
export { tokenOf, unitToken, tokenAt, isUnit } from './token.js';

export type { Place, EnvironmentPlace } from './place.js';
export { place, environmentPlace } from './place.js';

export type { Arc, ArcInput, ArcOutput, ArcInhibitor, ArcRead, ArcReset } from './arc.js';
export { inputArc, outputArc, inhibitorArc, readArc, resetArc, arcPlace, hasGuard, matchesGuard } from './arc.js';

export type { In, InOne, InExactly, InAll, InAtLeast } from './in.js';
export { one, exactly, all, atLeast, requiredCount, consumptionCount } from './in.js';

export type { NameId } from './name.js';
export { nameId } from './name.js';

export type { MatchSpec, MatchKey, KeyFn } from './match-spec.js';
export { matchSpec, matchKey, keyForPlace, matchCorrelates } from './match-spec.js';

export type { Out, OutAnd, OutXor, OutPlace, OutTimeout, OutForwardInput } from './out.js';
export { and, andPlaces, xor, xorPlaces, outPlace, timeout, timeoutPlace, forwardInput, allPlaces, enumerateBranches } from './out.js';

export type { Timing, TimingImmediate, TimingDeadline, TimingDelayed, TimingWindow, TimingExact } from './timing.js';
export { immediate, deadline, delayed, window, exact, earliest, latest, hasDeadline, MAX_DURATION_MS } from './timing.js';

export type { TransitionAction } from './transition-action.js';
export { passthrough, isPassthrough, transform, fork, transformFrom, transformAsync, produce, withTimeout } from './transition-action.js';

export type { LogFn } from './transition-context.js';
export { TransitionContext } from './transition-context.js';
export { TokenInput } from './token-input.js';
export type { OutputEntry } from './token-output.js';
export { TokenOutput } from './token-output.js';

export { Transition, TransitionBuilder } from './transition.js';
export { PetriNet, PetriNetBuilder } from './petri-net.js';

// Modular composition (spec/11-modular-composition.md). Scaffolding-level: types,
// builders, and validation only — `instantiate(...)` and `compose(...)` land in
// later tasks (#11, #12). See `subnet-def.ts` for status notes.
export type { Subnet } from './subnet.js';
export { closedSubnet, openSubnet } from './subnet.js';

export type { Port, PortDirection, Channel } from './interface.js';
export { Interface, InterfaceBuilder } from './interface.js';

export type { VerificationHarness, VerificationResult } from './subnet-def.js';
export { SubnetDef, SubnetDefBuilder } from './subnet-def.js';

export { Instance } from './instance.js';
export type { SubnetInstance } from './subnet-instance.js';

export { ComposeBindings } from './compose-bindings.js';

export { FusionSet, FusionSetBuilder } from './fusion-set.js';
