/**
 * Debug infrastructure for Petri net execution visualization and replay.
 *
 * <p>This package provides components for real-time debugging of Petri net executions:
 *
 * <h2>Core Components</h2>
 * <ul>
 *   <li>{@link org.libpetri.debug.DebugEventStore} - Event store with live tailing support</li>
 *   <li>{@link org.libpetri.debug.DebugSessionRegistry} - Registry for managing debug sessions</li>
 *   <li>{@link org.libpetri.debug.DebugProtocolHandler} - Framework-agnostic debug protocol handler</li>
 *   <li>{@link org.libpetri.debug.DebugAwareEventStore} - Composite event store for debug capture</li>
 * </ul>
 *
 * <h2>Protocol Types</h2>
 * <ul>
 *   <li>{@link org.libpetri.debug.DebugCommand} - Client-to-server commands</li>
 *   <li>{@link org.libpetri.debug.DebugResponse} - Server-to-client responses</li>
 *   <li>{@link org.libpetri.debug.NetEventConverter} - NetEvent to serializable form converter</li>
 * </ul>
 *
 * <h2>Usage</h2>
 * <pre>{@code
 * // Create debug session
 * var registry = new DebugSessionRegistry();
 * var session = registry.register("session-123", net);
 *
 * // Subscribe to live events
 * var sub = session.eventStore().subscribe(event -> {
 *     System.out.println("Event: " + event);
 * });
 *
 * // Use with NetExecutor
 * var executor = NetExecutor.builder(net, initial)
 *     .eventStore(session.eventStore())
 *     .build();
 * }</pre>
 *
 * @see org.libpetri.event.EventStore
 * @see org.libpetri.runtime.NetExecutor
 */
package org.libpetri.debug;
