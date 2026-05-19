package org.libpetri.doclet;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

/**
 * Shared HTML renderer for Petri Net diagrams in Javadoc.
 *
 * <p>{@link #renderDot(String, String)} / {@link #renderSubnetDot(String, String, String)}
 * embed the DOT source as a {@code data-dot} attribute on the container; the
 * inlined viewer bundle converts it to SVG client-side via an embedded
 * Graphviz WASM build. There is no server-side render path — host machines
 * never need Graphviz installed at doc-generation time.
 *
 * <p>CSS and JS are loaded from classpath resources and inlined into the
 * generated HTML, making the taglet fully self-contained with no external
 * file dependencies.
 *
 * @see PetriNetTaglet
 * @see SubnetTaglet
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
            throw new IllegalStateException("Failed to read classpath resource: " + path, e);
        }
    }

    /**
     * Renders a Petri-net diagram from its DOT source.
     *
     * <p>The DOT source is embedded as a {@code data-dot} attribute on the
     * container; the inlined viewer bundle mounts each container after DOM
     * ready. The CSS / JS / init script are guarded by an idempotency check
     * so they only execute once per page, even when multiple {@code @petrinet}
     * tags appear.
     *
     * @param title     optional title (null for no title)
     * @param dotSource the DOT source code; consumed by {@code LibpetriViewer.mount}
     *                  and also displayed in a collapsible details block
     * @return HTML markup with diagram controls
     */
    public static String renderDot(String title, String dotSource) {
        return render(title, /* headerHtml */ null, dotSource);
    }

    /**
     * Renders a subnet- or instance-aware diagram. Identical to
     * {@link #renderDot} apart from an extra {@code headerHtml} block (the
     * port/channel/params badge bar) prepended above the diagram, and the
     * CSS class {@code subnet-diagram} on the wrapper.
     *
     * @param title       diagram title (e.g. {@code "BoundedBuffer :: b1"})
     * @param headerHtml  the HTML produced by {@link SubnetHeader}
     * @param dotSource   the DOT source code
     * @return HTML markup
     */
    public static String renderSubnetDot(String title, String headerHtml, String dotSource) {
        return render(title, headerHtml, dotSource);
    }

    private static String render(String title, String headerHtml, String dotSource) {
        var titleHtml = title != null ? "<h4>%s</h4>\n".formatted(escapeHtml(title)) : "";
        var summaryText = title != null ? "View DOT Source" : "View Source";
        var diagramClass = headerHtml != null ? "petrinet-diagram subnet-diagram" : "petrinet-diagram";
        var headerBlock = headerHtml != null ? headerHtml : "";
        var hostHtml = "<div class=\"petrinet-diagram-viewer\" data-dot=\""
                + escapeHtml(dotSource) + "\"></div>";

        // `chrome:true` asks the viewer to inject its own legend, filter-chip
        // strip, cluster collapse, and fullscreen controls — no placeholders
        // are emitted from the Java side. Idempotency guard keys off
        // `_libpetriViewerInit` so the script only executes once per page.
        return """
            <style>%s</style>
            <script>if(!window._libpetriViewerInit){window._libpetriViewerInit=true;
            %s
            (function(){function mountAll(){if(!window.LibpetriViewer||!window.LibpetriViewer.mount)return;\
            var nodes=document.querySelectorAll('.petrinet-diagram-viewer[data-dot]:not([data-libpetri-mounted])');\
            nodes.forEach(function(n){n.setAttribute('data-libpetri-mounted','');\
            try{window.LibpetriViewer.mount(n.getAttribute('data-dot'),n,{chrome:true});}\
            catch(e){console.error('LibpetriViewer.mount failed',e);}});}
            if(document.readyState==='loading'){document.addEventListener('DOMContentLoaded',mountAll);}else{mountAll();}})();
            }</script>
            <div class="%s">
            %s%s%s
            <details>
            <summary>%s</summary>
            <pre><code>%s</code></pre>
            </details>
            </div>
            """.formatted(
                INLINE_CSS,
                INLINE_JS,
                diagramClass,
                titleHtml,
                headerBlock,
                hostHtml,
                summaryText,
                escapeHtml(dotSource));
    }

    /**
     * Escapes HTML special characters for safe embedding in HTML, including
     * within double-quoted attribute values.
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
