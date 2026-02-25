/**
 * Runtime execution engine for Typed Colored Time Petri Nets.
 *
 * <p>This package provides the execution infrastructure for running TCPN models.
 * The central component is {@link org.libpetri.runtime.NetExecutor},
 * which orchestrates token flow, transition firing, and timing behavior.
 *
 * <h2>Package Contents</h2>
 * <dl>
 *   <dt>{@link org.libpetri.runtime.NetExecutor}</dt>
 *   <dd>Main orchestrator that executes Petri nets. Manages the execution loop,
 *       transition enablement, firing order, and completion detection.</dd>
 *
 *   <dt>{@link org.libpetri.runtime.Marking}</dt>
 *   <dd>Mutable container for the token state (marking) of a net during execution.
 *       Maintains FIFO ordering of tokens per place.</dd>
 * </dl>
 *
 * <h2>Execution Model</h2>
 * <p>The executor follows a single-threaded orchestrator pattern:
 * <ol>
 *   <li>The orchestrator thread (caller of {@link org.libpetri.runtime.NetExecutor#run()})
 *       owns all Petri net state</li>
 *   <li>Transition actions execute asynchronously on a configurable {@link java.util.concurrent.ExecutorService}</li>
 *   <li>Actions signal completion via a lock-free queue</li>
 *   <li>The orchestrator applies marking changes after action completion</li>
 * </ol>
 *
 * <h2>Firing Semantics</h2>
 * <p>Transitions are fired according to these rules:
 * <ul>
 *   <li><strong>Enablement:</strong> A transition is enabled when all input arcs have
 *       matching tokens, all read arcs have tokens, and all inhibitor arcs' places
 *       are empty</li>
 *   <li><strong>Timing:</strong> An enabled transition can fire after its earliest
 *       firing time and must fire before its deadline</li>
 *   <li><strong>Priority:</strong> Higher priority transitions fire first; equal
 *       priorities use FIFO order based on enable time</li>
 *   <li><strong>Atomicity:</strong> Token consumption and production are atomic
 *       from the orchestrator's perspective</li>
 * </ul>
 *
 * <h2>Usage Example</h2>
 * <pre>{@code
 * // Define places and transitions
 * var start = Place.of("Start", Request.class);
 * var end = Place.of("End", Response.class);
 *
 * var process = Transition.builder("Process")
 *     .input(start)
 *     .output(end)
 *     .deadline(5000)  // 5 second deadline
 *     .action((in, out) -> {
 *         Request req = in.value(start);
 *         out.add(end, processRequest(req));
 *         return CompletableFuture.completedFuture(null);
 *     })
 *     .build();
 *
 * var net = PetriNet.builder("MyWorkflow")
 *     .transitions(process)
 *     .build();
 *
 * // Execute
 * var initial = Map.of(start, List.of(Token.of(new Request("data"))));
 * try (var executor = NetExecutor.create(net, initial)) {
 *     Marking result = executor.run();
 *     Response response = result.peekFirst(end).value();
 * }
 * }</pre>
 *
 * <h2>Event Sourcing</h2>
 * <p>The executor emits events to an {@link org.libpetri.event.EventStore}
 * for observability and replay. Events include transition enablement, firing,
 * completion, and token movement.
 *
 * @see org.libpetri.core
 * @see org.libpetri.event
 */
package org.libpetri.runtime;
