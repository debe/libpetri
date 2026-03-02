/**
 * Coloured Time Petri Net (CTPN) - A Java library for modeling and
 * executing workflow systems with formal timing semantics.
 *
 * <h2>What is CTPN?</h2>
 * <p>CTPN extends classical Petri nets with three key features:
 * <ul>
 *   <li><strong>Typed tokens:</strong> Tokens carry typed data values (not just markers),
 *       enabling type-safe data flow through the workflow.</li>
 *   <li><strong>Colored tokens:</strong> Places are typed, and tokens are distinguished
 *       by their value, enabling conditional routing and data transformation.</li>
 *   <li><strong>Time intervals:</strong> Transitions have firing intervals [earliest, deadline]
 *       that constrain when they can fire, enabling formal timing analysis.</li>
 * </ul>
 *
 * <h2>Theoretical Foundation</h2>
 * <p>CTPN builds on several Petri net extensions:
 * <ul>
 *   <li><strong>Time Petri Nets (TPN):</strong> Merlin &amp; Farber (1976) - adds time
 *       intervals to transitions</li>
 *   <li><strong>Colored Petri Nets (CPN):</strong> Jensen (1981) - adds typed tokens
 *       and arc expressions</li>
 *   <li><strong>High-level Petri Nets:</strong> ISO/IEC 15909 - standardized CPN semantics</li>
 * </ul>
 *
 * <h2>Package Structure</h2>
 * <dl>
 *   <dt>{@link org.libpetri.core}</dt>
 *   <dd>Core model classes: {@link org.libpetri.core.Place Place},
 *       {@link org.libpetri.core.Token Token},
 *       {@link org.libpetri.core.Transition Transition},
 *       {@link org.libpetri.core.Arc Arc},
 *       {@link org.libpetri.core.PetriNet PetriNet}</dd>
 *
 *   <dt>{@link org.libpetri.runtime}</dt>
 *   <dd>Execution engine: {@link org.libpetri.runtime.NetExecutor NetExecutor}
 *       orchestrates token flow and transition firing with async action support</dd>
 *
 *   <dt>{@link org.libpetri.event}</dt>
 *   <dd>Event sourcing: {@link org.libpetri.event.NetEvent NetEvent} hierarchy
 *       and {@link org.libpetri.event.EventStore EventStore} for observability</dd>
 *
 *   <dt>{@link org.libpetri.analysis}</dt>
 *   <dd>Formal analysis: {@link org.libpetri.analysis.StateSpaceAnalyzer StateSpaceAnalyzer}
 *       for reachability, deadlock detection, and liveness verification</dd>
 *
 *   <dt>{@link org.libpetri.export}</dt>
 *   <dd>Export formats: {@link org.libpetri.export.DotExporter DotExporter}
 *       for visualization</dd>
 * </dl>
 *
 * <h2>Quick Start</h2>
 * <pre>{@code
 * // 1. Define places (typed containers for tokens)
 * var request = Place.of("Request", UserRequest.class);
 * var validated = Place.of("Validated", UserRequest.class);
 * var response = Place.of("Response", ApiResponse.class);
 *
 * // 2. Define transitions (actions with timing constraints)
 * var validate = Transition.builder("Validate")
 *     .input(request)
 *     .output(validated)
 *     .deadline(500)  // must complete within 500ms
 *     .action((in, out) -> {
 *         UserRequest req = in.value(request);
 *         if (isValid(req)) {
 *             out.add(validated, req);
 *         }
 *         return CompletableFuture.completedFuture(null);
 *     })
 *     .build();
 *
 * var process = Transition.builder("Process")
 *     .input(validated)
 *     .output(response)
 *     .deadline(5000)
 *     .action((in, out) -> {
 *         UserRequest req = in.value(validated);
 *         return callApi(req).thenAccept(resp -> out.add(response, resp));
 *     })
 *     .build();
 *
 * // 3. Build the net
 * var net = PetriNet.builder("RequestProcessor")
 *     .transitions(validate, process)
 *     .build();
 *
 * // 4. Execute with initial tokens
 * var initial = Map.of(request, List.of(Token.of(new UserRequest("data"))));
 * try (var executor = NetExecutor.create(net, initial)) {
 *     Marking result = executor.run();
 *     ApiResponse resp = result.peekFirst(response).value();
 * }
 * }</pre>
 *
 * <h2>Arc Types</h2>
 * <p>CTPN supports five arc types for modeling different control flow patterns:
 * <table border="1">
 *   <caption>Arc types and their semantics</caption>
 *   <tr><th>Arc Type</th><th>Notation</th><th>Semantics</th></tr>
 *   <tr><td>Input</td><td>place → transition</td><td>Consumes token (enables when token present)</td></tr>
 *   <tr><td>Output</td><td>transition → place</td><td>Produces token after firing</td></tr>
 *   <tr><td>Inhibitor</td><td>place ⊸ transition</td><td>Blocks firing when token present</td></tr>
 *   <tr><td>Read</td><td>place ⟷ transition</td><td>Reads without consuming (test arc)</td></tr>
 *   <tr><td>Reset</td><td>place ⟿ transition</td><td>Clears all tokens from place</td></tr>
 * </table>
 *
 * <h2>Firing Semantics</h2>
 * <p>A transition fires according to these rules:
 * <ol>
 *   <li><strong>Enablement:</strong> All input arcs have matching tokens, all read arcs
 *       have tokens, all inhibitor arcs' places are empty</li>
 *   <li><strong>Timing:</strong> Enabled for at least {@code earliest} duration; must fire
 *       before {@code deadline} (urgent semantics)</li>
 *   <li><strong>Priority:</strong> Higher priority transitions fire first when multiple
 *       are ready</li>
 *   <li><strong>Atomicity:</strong> Token consumption and production are atomic</li>
 * </ol>
 *
 * <h2>Formal Properties</h2>
 * <p>CTPN models can be analyzed for:
 * <ul>
 *   <li><strong>Reachability:</strong> Can a specific marking be reached?</li>
 *   <li><strong>Liveness:</strong> Can every transition eventually fire?</li>
 *   <li><strong>Deadlock-freedom:</strong> Is the net free from deadlocks?</li>
 *   <li><strong>Boundedness:</strong> Is the number of tokens in each place bounded?</li>
 *   <li><strong>Timing bounds:</strong> What are the min/max completion times?</li>
 * </ul>
 *
 * <h2>Thread Safety</h2>
 * <p>The library follows a single-threaded orchestrator pattern:
 * <ul>
 *   <li>Model classes ({@code Place}, {@code Transition}, {@code PetriNet}) are immutable
 *       and thread-safe</li>
 *   <li>{@code NetExecutor} owns all runtime state; the orchestrator thread (caller of
 *       {@code run()}) is the only thread that modifies marking</li>
 *   <li>Transition actions execute asynchronously but must not access marking directly</li>
 *   <li>{@code EventStore} implementations must be thread-safe</li>
 * </ul>
 *
 * @see org.libpetri.core
 * @see org.libpetri.runtime.NetExecutor
 */
package org.libpetri;
