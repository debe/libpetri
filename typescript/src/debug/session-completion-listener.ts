/**
 * Listener notified when a debug session completes.
 */
import type { DebugSession } from './debug-session-registry.js';

export type SessionCompletionListener = (session: DebugSession) => void;
