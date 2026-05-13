package org.libpetri.doclet;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

/**
 * Shared HTML renderer for Petri Net diagrams in Javadoc.
 *
 * <p>Generates HTML that hosts the canonical {@code LibpetriViewer} bundle
 * (built from {@code typescript/src/viewer/}). The bundle handles DOT &rarr;
 * SVG rendering client-side (via an inlined Graphviz WASM build), wires
 * pan/zoom, and (with {@code chrome: true}) injects the cluster legend,
 * filter-chip strip, and cluster collapse controls automatically.
 *
 * <p>The renderer no longer pre-renders SVG via the {@code dot} command-line
 * tool: the DOT source is embedded as a {@code data-dot} attribute on the
 * container, and the viewer renders it on page load. This removes the build
 * dependency on Graphviz being installed on the doc-generation host.
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
            throw new IllegalStateException("Failed to load classpath resource: " + path, e);
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
        return renderInternal(title, /* headerHtml */ null, dotSource);
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
        return renderInternal(title, headerHtml, dotSource);
    }

    private static String renderInternal(String title, String headerHtml, String dotSource) {
        var titleHtml = title != null ? "<h4>%s</h4>\n".formatted(escapeHtml(title)) : "";
        var summaryText = title != null ? "View DOT Source" : "View Source";
        var diagramClass = headerHtml != null ? "petrinet-diagram subnet-diagram" : "petrinet-diagram";
        var headerBlock = headerHtml != null ? headerHtml : "";

        // The CSS, the LibpetriViewer bundle, and the init script are emitted
        // once per page (idempotency guard keys off `window.LibpetriViewer`,
        // which the inlined bundle defines synchronously). After DOM ready,
        // the init script finds every `.petrinet-diagram-viewer[data-dot]`
        // container that hasn't been mounted yet and calls
        // `LibpetriViewer.mount(dot, container, { chrome: true })`. The
        // `chrome: true` flag asks the viewer to inject its own legend,
        // filter-chip strip, and cluster collapse controls — we no longer
        // emit placeholders for these on the Java side.
        //
        // TODO(viewer): fullscreen-button — the new canonical viewer does
        // not expose a fullscreen toggle (the old hand-written IIFE did, via
        // PetriNetDiagrams.toggleFullscreen). If/when the viewer adds it,
        // re-introduce a button here that invokes the new API.
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
            %s%s<div class="petrinet-diagram-viewer" data-dot="%s"></div>
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
                escapeHtml(dotSource),
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
