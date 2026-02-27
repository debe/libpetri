package org.libpetri.export;

import org.libpetri.core.PetriNet;

/**
 * Convenience exporter: PetriNet to DOT (Graphviz) format.
 *
 * <p>Combines {@link PetriNetGraphMapper} and {@link DotRenderer} into a
 * single-call API for common use cases.
 *
 * <h2>Usage Example</h2>
 * <pre>{@code
 * var net = PetriNet.builder("MyWorkflow")
 *     .transitions(t1, t2, t3)
 *     .build();
 *
 * // Default configuration
 * String dot = DotExporter.export(net);
 *
 * // Custom configuration
 * String dot = DotExporter.export(net, ExportConfig.minimal());
 * }</pre>
 */
public final class DotExporter {

    private DotExporter() {}

    /**
     * Exports a PetriNet to DOT format with default configuration.
     *
     * @param net the Petri net to export
     * @return DOT string suitable for rendering with Graphviz
     */
    public static String export(PetriNet net) {
        return export(net, ExportConfig.DEFAULT);
    }

    /**
     * Exports a PetriNet to DOT format with custom configuration.
     *
     * @param net the Petri net to export
     * @param config export configuration
     * @return DOT string suitable for rendering with Graphviz
     */
    public static String export(PetriNet net, ExportConfig config) {
        return DotRenderer.render(PetriNetGraphMapper.map(net, config));
    }

    /**
     * Sanitizes a name for use as a graph node ID.
     *
     * @param name the name to sanitize
     * @return the sanitized name
     */
    public static String sanitize(String name) {
        return name.replaceAll("[^a-zA-Z0-9_]", "_");
    }
}
