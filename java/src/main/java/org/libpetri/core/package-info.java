/**
 * Core domain model for Coloured Time Petri Nets (CTPN).
 *
 * <h2>Overview</h2>
 * This package provides a type-safe, immutable model for defining and executing
 * Time Petri Nets with colored (typed) tokens. It combines three Petri net extensions:
 * <ul>
 *   <li><b>Colored Petri Nets</b> - tokens carry typed data values</li>
 *   <li><b>Time Petri Nets</b> - transitions have firing intervals [earliest, deadline]</li>
 *   <li><b>Extended arcs</b> - inhibitor, read, and reset arcs for complex control flow</li>
 * </ul>
 *
 * <h2>Core Concepts</h2>
 *
 * <h3>Places and Tokens</h3>
 * {@link org.libpetri.core.Place Places} are typed containers that hold
 * {@link org.libpetri.core.Token Tokens}. Each place declares the type of
 * values it accepts, providing compile-time type safety:
 * <pre>{@code
 * Place<String> input = Place.of("Input", String.class);
 * Place<Integer> output = Place.of("Output", Integer.class);
 *
 * Token<String> token = Token.of("hello");
 * }</pre>
 *
 * <h3>Transitions</h3>
 * {@link org.libpetri.core.Transition Transitions} consume tokens from input
 * places and produce tokens to output places. They are configured via a fluent builder:
 * <pre>{@code
 * var transition = Transition.builder("Process")
 *     .input(input)                           // consume from input place
 *     .output(output)                         // produce to output place
 *     .deadline(Duration.ofSeconds(5))        // must complete within 5s
 *     .action((in, out) -> {                  // action to execute
 *         String value = in.value(input);     // type-safe access
 *         out.add(output, value.length());    // type-safe output
 *         return CompletableFuture.completedFuture(null);
 *     })
 *     .build();
 * }</pre>
 *
 * <h3>Arc Types</h3>
 * {@link org.libpetri.core.Arc Arcs} connect places to transitions with
 * different semantics:
 * <ul>
 *   <li><b>Input</b> - consumes a token when transition fires (required for enabling)</li>
 *   <li><b>Output</b> - produces a token when transition completes</li>
 *   <li><b>Inhibitor</b> - blocks transition if place has tokens</li>
 *   <li><b>Read</b> - requires token but doesn't consume it</li>
 *   <li><b>Reset</b> - removes ALL tokens from place when firing</li>
 * </ul>
 *
 * Input arcs support guard predicates for colored Petri net pattern matching:
 * <pre>{@code
 * .inputWhen(results, r -> r instanceof Success)  // only match Success tokens
 * }</pre>
 *
 * <h3>Time Semantics</h3>
 * {@link org.libpetri.core.FiringInterval FiringInterval} defines when a
 * transition may or must fire after becoming enabled:
 * <ul>
 *   <li>{@code [0, deadline]} - may fire immediately, must fire before deadline</li>
 *   <li>{@code [delay, delay]} - fires exactly after delay (deterministic)</li>
 *   <li>{@code [0, infinity]} - unconstrained (classical Petri net behavior)</li>
 * </ul>
 *
 * <h3>Transition Actions</h3>
 * {@link org.libpetri.core.TransitionAction TransitionAction} defines the
 * computation performed when a transition fires. Actions receive type-safe access
 * to consumed tokens via {@link org.libpetri.core.TokenInput TokenInput}
 * and produce outputs via {@link org.libpetri.core.TokenOutput TokenOutput}:
 * <pre>{@code
 * .action((in, out) -> {
 *     // Read inputs (type-safe)
 *     Request req = in.value(requestPlace);
 *     Context ctx = in.value(contextPlace);
 *
 *     // Async processing - return outputs through the future
 *     return service.process(req, ctx)
 *         .thenApply(result -> {
 *             out.add(resultPlace, result);
 *             return out;
 *         });
 * })
 * }</pre>
 *
 * <h3>Building a Net</h3>
 * {@link org.libpetri.core.PetriNet PetriNet} assembles places and transitions
 * into an immutable, reusable definition:
 * <pre>{@code
 * var net = PetriNet.builder("MyWorkflow")
 *     .transitions(receiveRequest, processRequest, sendResponse)
 *     .build();  // places are auto-collected from transition arcs
 * }</pre>
 *
 * <h2>Design Principles</h2>
 * <ul>
 *   <li><b>Immutability</b> - all core types are immutable after construction</li>
 *   <li><b>Type safety</b> - places and tokens are generically typed</li>
 *   <li><b>Identity semantics</b> - Transition uses object identity (not name-based)</li>
 *   <li><b>Separation of concerns</b> - net definition vs. execution (see runtime package)</li>
 * </ul>
 *
 * @see org.libpetri.runtime.NetExecutor NetExecutor for execution
 */
package org.libpetri.core;
