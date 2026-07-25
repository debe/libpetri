/**
 * Runtime execution engine for Coloured Time Petri Nets.
 *
 * <p>This package provides the execution infrastructure for running CTPN models,
 * orchestrating token flow, transition firing, and timing behavior.
 *
 * <h2>Package Contents</h2>
 * <dl>
 *   <dt>{@link org.libpetri.runtime.PrecompiledNetExecutor}</dt>
 *   <dd>The production executor. Flat-array/opcode representation, ring-buffer token
 *       storage, priority-partitioned ready queues.</dd>
 *
 *   <dt>{@link org.libpetri.runtime.BitmapNetExecutor}</dt>
 *   <dd>The reference executor: clear, canonical firing semantics. The precompiled
 *       executor must stay behaviorally identical to it.</dd>
 *
 *   <dt>{@link org.libpetri.runtime.Marking}</dt>
 *   <dd>Mutable container for the token state (marking) of a net during execution.
 *       Maintains FIFO ordering of tokens per place.</dd>
 * </dl>
 *
 * <h2>Execution Model</h2>
 * <p>The executors follow a single-threaded orchestrator pattern:
 * <ol>
 *   <li>The orchestrator thread (caller of {@code run()}) owns all Petri net state</li>
 *   <li><b>Transition actions are invoked inline, on that same thread.</b> No executor
 *       dispatches them; concurrency comes from whatever drives the
 *       {@link java.util.concurrent.CompletionStage} an action returns. A configured
 *       {@link java.util.concurrent.ExecutorService} hosts only the orchestrator loop
 *       under {@code run(Duration)}.</li>
 *   <li>Whatever thread completes an action signals through a lock-free queue</li>
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
 * try (var executor = BitmapNetExecutor.builder(net, initial).build()) {
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
