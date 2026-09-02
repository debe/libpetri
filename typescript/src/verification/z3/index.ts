export { runZ3Spacer } from './spacer-runner.js';
export type { QueryResult, QueryProven, QueryViolated, QueryUnknown } from './spacer-runner.js';
export {
  resolveZ3, z3SolverAt, z3Available, runZ3Text, Z3Unavailable, Z3ProcessError,
  parseZ3Version, formatZ3Version, MIN_Z3_VERSION, Z3_ENV, DUMP_ENV,
} from './z3-process.js';
export type { Z3Solver, Z3Version, Z3Reply, Z3Exit } from './z3-process.js';
export { encode, encodeStepRelationSmt2 } from './smt-encoder.js';
export type { SmtEncoding } from './smt-encoder.js';
export { checkCertificate, vcScript } from './certificate-checker.js';
export type { CertificateCheckOutcome, CertificateVc } from './certificate-checker.js';
export { decode, decodeStateSet } from './counterexample-decoder.js';
export type { DecodedTrace } from './counterexample-decoder.js';
// Only the replay entry point is package API; the abstract-semantics primitives
// (enabledA/fireA/injectA/successors/satisfiesBad, vectorize/toMarkingState,
// stateKey/stepName) and the encoder's sub-builders stay module-internal —
// tests import them from their defining module.
export { replayCounterexample } from './abstract-replayer.js';
export type {
  AbstractState, ReplayStep, ReplayOptions, ReplayOutcome,
} from './abstract-replayer.js';
