/**
 * Open-net verification: a subnet checked in isolation against a contract, with its ports
 * played by the environment ([VER-022]). Entry point: {@link verifyOpenNet}.
 *
 * @module verification/open-net
 */
export { OpenNetContract, OpenNetContractBuilder } from './contract.js';
export type { ArrivalGroup, CountClause, DesignedTerminal } from './contract.js';
export { closeOpenNet } from './closure.js';
export type { ClosedNet, EnvironmentStep } from './closure.js';
export { verifyOpenNet } from './verify-open-net.js';
export type { OpenNetOptions } from './verify-open-net.js';
export type {
  ContractViolation, ContractViolationKind, OpenNetResult, OpenNetRoute, PortChange, PortStep,
} from './result.js';
