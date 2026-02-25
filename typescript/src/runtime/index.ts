/**
 * Runtime execution engine: bitmap-based executor, marking state, and output validation.
 *
 * The primary entry point is `BitmapNetExecutor` — construct with a `PetriNet`, initial
 * tokens, and options, then call `run()` to execute. Supports environment place injection
 * for external event-driven nets.
 *
 * @module runtime
 */
export { Marking } from './marking.js';
export type { GuardSpec } from './marking.js';
export { CompiledNet, setBit, clearBit, testBit, containsAll, intersects } from './compiled-net.js';
export type { CardinalityCheck } from './compiled-net.js';
export { BitmapNetExecutor } from './bitmap-net-executor.js';
export type { BitmapNetExecutorOptions } from './bitmap-net-executor.js';
export type { PetriNetExecutor } from './petri-net-executor.js';
export { OutViolationError } from './out-violation-error.js';
export { validateOutSpec, produceTimeoutOutput } from './executor-support.js';
