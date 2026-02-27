/**
 * libpetri — Coloured Time Petri Net engine for TypeScript.
 *
 * Re-exports core (net definitions), runtime (bitmap executor), and event (observation)
 * modules. For diagram export, import from `libpetri/export`. For formal verification
 * via Z3, import from `libpetri/verification`.
 *
 * @module libpetri
 */
export * from './core/index.js';
export * from './runtime/index.js';
export * from './event/index.js';
