package org.libpetri.doclet;

/**
 * Shared HTML renderer for Petri Net diagrams in Javadoc.
 *
 * <p>Generates consistent HTML markup with interactive controls
 * for zoom, pan, and fullscreen functionality.
 *
 * @see MermaidTaglet
 * @see PetriNetTaglet
 */
public final class DiagramRenderer {

    private DiagramRenderer() {}

    /**
     * Renders a Mermaid diagram without a title.
     *
     * @param mermaidCode the Mermaid diagram code
     * @return HTML markup with diagram controls
     */
    public static String render(String mermaidCode) {
        return render(null, mermaidCode);
    }

    /**
     * Renders a Mermaid diagram with an optional title.
     *
     * @param title optional title (null for no title)
     * @param mermaidCode the Mermaid diagram code
     * @return HTML markup with diagram controls
     */
    public static String render(String title, String mermaidCode) {
        var escaped = escapeHtml(mermaidCode);
        var titleHtml = title != null ? "<h4>%s</h4>\n".formatted(title) : "";
        var summaryText = title != null ? "View Mermaid Source" : "View Source";

        return """
            <div class="petrinet-diagram">
            %s<div class="diagram-container">
            <div class="diagram-controls">
            <button class="diagram-btn btn-reset" title="Reset zoom">Reset</button>
            <button class="diagram-btn btn-fullscreen" onclick="PetriNetDiagrams.toggleFullscreen(this)">Fullscreen</button>
            </div>
            <pre class="mermaid">
            %s
            </pre>
            </div>
            <details>
            <summary>%s</summary>
            <pre><code>%s</code></pre>
            </details>
            </div>
            """.formatted(titleHtml, mermaidCode, summaryText, escaped);
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
