/**
 * Exporters for converting TCPN models to external formats.
 *
 * <p>This package provides exporters for visualization and formal analysis
 * of Typed Colored Time Petri Net models.
 *
 * <h2>Available Exporters</h2>
 * <dl>
 *   <dt>{@link org.libpetri.export.MermaidExporter}</dt>
 *   <dd>Exports to <a href="https://mermaid.js.org/">Mermaid</a> flowchart format
 *       for visualization in markdown, documentation, and web pages.</dd>
 *
 *   <dt>{@link org.libpetri.export.SirioExporter}</dt>
 *   <dd>Exports to <a href="https://github.com/oris-tool/sirio">Sirio/ORIS</a>
 *       object model for formal timing analysis, reachability checking,
 *       and state space exploration.</dd>
 * </dl>
 *
 * <h2>Usage Examples</h2>
 *
 * <h3>Visualization with Mermaid</h3>
 * <pre>{@code
 * var net = PetriNet.builder("Workflow").transitions(t1, t2, t3).build();
 *
 * // Generate diagram
 * String mermaid = MermaidExporter.export(net);
 *
 * // Output can be rendered in GitHub markdown:
 * // ```mermaid
 * // flowchart TB
 * //     Start --> t_Process --> End
 * // ```
 * }</pre>
 *
 * <h3>Formal Analysis with Sirio</h3>
 * <pre>{@code
 * var sirio = SirioExporter.export(net, "StartPlace");
 *
 * // Run timing analysis
 * var analysis = TimedAnalysis.builder().build();
 * var graph = analysis.compute(sirio.net(), sirio.initialMarking());
 *
 * // Check properties
 * boolean canReachEnd = graph.getNodes().stream()
 *     .anyMatch(n -> n.getState().getTokens("EndPlace") > 0);
 * }</pre>
 *
 * <h2>Format Comparison</h2>
 * <table border="1">
 *   <caption>Exporter capabilities</caption>
 *   <tr><th>Feature</th><th>Mermaid</th><th>Sirio</th></tr>
 *   <tr><td>Visualization</td><td>Yes</td><td>No</td></tr>
 *   <tr><td>Formal Analysis</td><td>No</td><td>Yes</td></tr>
 *   <tr><td>Timing Analysis</td><td>Display only</td><td>Full analysis</td></tr>
 *   <tr><td>Token Types</td><td>Display only</td><td>Ignored</td></tr>
 *   <tr><td>Guards</td><td>Display only</td><td>Ignored</td></tr>
 * </table>
 *
 * @see org.libpetri.core.PetriNet
 */
package org.libpetri.export;
