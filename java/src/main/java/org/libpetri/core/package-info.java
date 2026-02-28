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
 *     .inputs(Arc.In.one(input))                // consume from input place
 *     .outputs(Arc.Out.and(output))             // produce to output place
 *     .timing(Timing.deadline(Duration.ofSeconds(5)))
 *     .action((in, out) -> {
 *         String value = in.value(input);       // type-safe access
 *         out.add(output, value.length());      // type-safe output
 *         return CompletableFuture.completedFuture(null);
 *     })
 *     .build();
 * }</pre>
 *
 * <h3>Arc Types</h3>
 * {@link org.libpetri.core.Arc Arcs} connect places to transitions with
 * different semantics:
 * <ul>
 *   <li><b>{@link org.libpetri.core.Arc.In}</b> - input specs with cardinality (one, exactly, all, atLeast)</li>
 *   <li><b>{@link org.libpetri.core.Arc.Out}</b> - output specs with split semantics (AND, XOR, timeout)</li>
 *   <li><b>Inhibitor</b> - blocks transition if place has tokens</li>
 *   <li><b>Read</b> - requires token but doesn't consume it</li>
 *   <li><b>Reset</b> - removes ALL tokens from place when firing</li>
 * </ul>
 *
 * <h3>Time Semantics</h3>
 * {@link org.libpetri.core.Timing Timing} defines when a transition may or
 * must fire after becoming enabled:
 * <ul>
 *   <li>{@code immediate()} - may fire as soon as enabled (default)</li>
 *   <li>{@code deadline(by)} - must fire before deadline</li>
 *   <li>{@code delayed(after)} - must wait before firing</li>
 *   <li>{@code window(earliest, latest)} - classical TPN interval</li>
 *   <li>{@code exact(at)} - fires at precisely the specified time</li>
 * </ul>
 *
 * <h3>Transition Actions</h3>
 * {@link org.libpetri.core.TransitionAction TransitionAction} defines the
 * computation performed when a transition fires. Actions receive type-safe access
 * to consumed tokens via {@link org.libpetri.core.TokenInput TokenInput}
 * and produce outputs via {@link org.libpetri.core.TokenOutput TokenOutput}:
 * <pre>{@code
 * .action((in, out) -> {
 *     Request req = in.value(requestPlace);
 *     return service.process(req)
 *         .thenAccept(result -> out.add(resultPlace, result));
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
