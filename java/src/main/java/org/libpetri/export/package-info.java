/**
 * Exporters for converting CTPN models to external formats.
 *
 * <p>This package provides exporters for visualization and formal analysis
 * of Coloured Time Petri Net models.
 *
 * <h2>Available Exporters</h2>
 * <dl>
 *   <dt>{@link org.libpetri.export.DotExporter}</dt>
 *   <dd>Exports to <a href="https://graphviz.org/">DOT/Graphviz</a> format with proper
 *       Petri net visual conventions (circles for places, bars for transitions).
 *       Uses a layered architecture: {@link org.libpetri.export.PetriNetGraphMapper} maps
 *       to a format-agnostic {@link org.libpetri.export.graph.Graph}, then
 *       {@link org.libpetri.export.DotRenderer} renders to DOT string.</dd>
 *
 *   <dt>{@link org.libpetri.export.MermaidExporter} (deprecated)</dt>
 *   <dd>Exports to <a href="https://mermaid.js.org/">Mermaid</a> flowchart format.
 *       Retained for backward compatibility; prefer {@link org.libpetri.export.DotExporter}.</dd>
 *
 * </dl>
 *
 * <h2>Usage Examples</h2>
 *
 * <h3>Visualization with DOT</h3>
 * <pre>{@code
 * var net = PetriNet.builder("Workflow").transitions(t1, t2, t3).build();
 *
 * // Generate DOT diagram
 * String dot = DotExporter.export(net);
 *
 * // Render with Graphviz (CLI or @viz-js/viz WASM)
 * // dot -Tsvg -o workflow.svg
 * }</pre>
 *
 * <h2>Format Comparison</h2>
 * <table border="1">
 *   <caption>Exporter capabilities</caption>
 *   <tr><th>Feature</th><th>DOT</th><th>Mermaid</th></tr>
 *   <tr><td>Visualization</td><td>Yes</td><td>Yes</td></tr>
 *   <tr><td>PN conventions</td><td>Yes (circles/bars)</td><td>No (stadiums/rects)</td></tr>
 *   <tr><td>Animation support</td><td>Yes (via SVG)</td><td>Limited</td></tr>
 *   <tr><td>Env place styling</td><td>Yes (dashed)</td><td>No</td></tr>
 * </table>
 *
 * @see org.libpetri.core.PetriNet
 */
package org.libpetri.export;
