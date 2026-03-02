package org.libpetri.doclet;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

/**
 * Shared HTML renderer for Petri Net diagrams in Javadoc.
 *
 * <p>Generates consistent HTML markup with interactive controls
 * for zoom, pan, and fullscreen functionality. Accepts pre-rendered SVG
 * from the {@code dot} command-line tool.
 *
 * <p>CSS and JS are loaded from classpath resources and inlined into the
 * generated HTML, making the taglet fully self-contained with no external
 * file dependencies.
 *
 * @see PetriNetTaglet
 */
public final class DiagramRenderer {

    private static final String INLINE_CSS = loadResource("/javadoc/petrinet-diagrams.css");
    private static final String INLINE_JS = loadResource("/javadoc/petrinet-diagrams.js");

    private DiagramRenderer() {}

    private static String loadResource(String path) {
        try (InputStream in = DiagramRenderer.class.getResourceAsStream(path)) {
            if (in == null) {
                throw new IllegalStateException("Missing classpath resource: " + path);
            }
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new IllegalStateException("Failed to load classpath resource: " + path, e);
        }
    }

    /**
     * Renders a pre-built SVG diagram with an optional title.
     *
     * <p>Inlines CSS and JS from classpath resources. The JS is guarded by
     * an idempotency check so it only executes once per page, even when
     * multiple {@code @petrinet} tags appear.
     *
     * @param title optional title (null for no title)
     * @param svgContent the SVG markup (from {@code dot -Tsvg})
     * @param dotSource the DOT source code for display in a collapsible details block
     * @return HTML markup with diagram controls
     */
    public static String renderSvg(String title, String svgContent, String dotSource) {
        var titleHtml = title != null ? "<h4>%s</h4>\n".formatted(escapeHtml(title)) : "";
        var summaryText = title != null ? "View DOT Source" : "View Source";

        return """
            <style>%s</style>
            <script>if(!window._petriNetDiagramsInit){window._petriNetDiagramsInit=true;
            %s
            }</script>
            <div class="petrinet-diagram">
            %s<div class="diagram-container">
            <div class="diagram-controls">
            <button class="diagram-btn btn-reset" title="Reset zoom">Reset</button>
            <button class="diagram-btn btn-fullscreen" onclick="PetriNetDiagrams.toggleFullscreen(this)">Fullscreen</button>
            </div>
            %s
            </div>
            <details>
            <summary>%s</summary>
            <pre><code>%s</code></pre>
            </details>
            </div>
            """.formatted(INLINE_CSS, INLINE_JS, titleHtml, svgContent, summaryText, escapeHtml(dotSource));
    }

    /**
     * Escapes HTML special characters for safe embedding in HTML.
     *
     * @param text the text to escape
     * @return HTML-escaped text
     */
    public static String escapeHtml(String text) {
        return text
            .replace("&", "&amp;")
            .replace("<", "&lt;")
            .replace(">", "&gt;")
            .replace("\"", "&quot;");
    }
}
