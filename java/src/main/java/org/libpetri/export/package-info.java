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
 *
 * @see org.libpetri.core.PetriNet
 */
package org.libpetri.export;
