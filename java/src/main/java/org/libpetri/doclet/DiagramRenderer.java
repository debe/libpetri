package org.libpetri.doclet;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.Optional;

/**
 * Shared HTML renderer for Petri Net diagrams in Javadoc.
 *
 * <p>Two render paths are exposed:
 * <ul>
 *   <li>{@link #renderDot(String, String)} / {@link #renderSubnetDot(String, String, String)}
 *       — client-side render. The DOT source is embedded as a {@code data-dot}
 *       attribute on the container; the inlined viewer bundle converts it to
 *       SVG client-side via an embedded Graphviz WASM build.</li>
 *   <li>{@link #renderSvg(String, String, String)} /
 *       {@link #renderSubnetSvg(String, String, String, String)} — pre-rendered
 *       path. The SVG was produced at build time (typically by piping the DOT
 *       source through the {@code dot} command-line tool) and is embedded raw
 *       inside the container. The viewer bundle skips its viz call and only
 *       wires up pan/zoom + chrome.</li>
 * </ul>
 *
 * <p>The pre-rendered path drops page-load latency dramatically because the
 * browser does not need to compile and execute the Graphviz WASM blob for each
 * diagram. It is selected by {@link PetriNetTaglet} when {@code dot} is
 * available on {@code PATH} at doc-generation time; otherwise the taglet
 * gracefully falls back to {@link #renderDot}.
 *
 * <p>CSS and JS are loaded from classpath resources and inlined into the
 * generated HTML, making the taglet fully self-contained with no external
 * file dependencies. The pre-rendered path inlines the slim
 * {@code petrinet-diagrams-static.js} bundle (which stubs out the Graphviz
 * WASM blob); if the slim bundle is absent from the classpath the renderer
 * logs a warning and falls back to the full bundle. The CSS is shared across
 * both paths.
 *
 * @see PetriNetTaglet
 * @see SubnetTaglet
 */
public final class DiagramRenderer {

    private static final System.Logger LOG = System.getLogger(DiagramRenderer.class.getName());

    private static final String INLINE_CSS = loadResource("/javadoc/petrinet-diagrams.css");
    private static final String INLINE_JS = loadResource("/javadoc/petrinet-diagrams.js");
    private static final String INLINE_STATIC_JS = loadStaticResourceOrFallback(
            "/javadoc/petrinet-diagrams-static.js", INLINE_JS);

    private DiagramRenderer() {}

    private static String loadResource(String path) {
        var opt = tryLoadResource(path);
        if (opt.isEmpty()) {
            throw new IllegalStateException("Missing classpath resource: " + path);
        }
        return opt.get();
    }

    private static Optional<String> tryLoadResource(String path) {
        try (InputStream in = DiagramRenderer.class.getResourceAsStream(path)) {
            if (in == null) {
                return Optional.empty();
            }
            return Optional.of(new String(in.readAllBytes(), StandardCharsets.UTF_8));
        } catch (IOException e) {
            return Optional.empty();
        }
    }

    private static String loadStaticResourceOrFallback(String path, String fallback) {
        var opt = tryLoadResource(path);
        if (opt.isEmpty()) {
            LOG.log(System.Logger.Level.WARNING,
                "Slim viewer bundle ''{0}'' not on classpath — falling back to the full bundle "
              + "(performance unchanged until the slim bundle is published).", path);
            return fallback;
        }
        return opt.get();
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
        return render(title, /* headerHtml */ null, dotSource, dotBody(dotSource));
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
        return render(title, headerHtml, dotSource, dotBody(dotSource));
    }

    /**
     * Renders a Petri-net diagram from pre-rendered SVG.
     *
     * <p>The SVG content is embedded raw inside the viewer container; the
     * viewer bundle wires up pan/zoom and chrome without invoking its
     * Graphviz path. The original DOT source is still surfaced inside the
     * collapsible {@code <details>} block beneath the diagram.
     *
     * @param title       optional title (null for no title)
     * @param svgContent  pre-rendered SVG (embedded raw, not escaped)
     * @param dotSource   the DOT source code (displayed in the details block)
     * @return HTML markup with diagram controls
     */
    public static String renderSvg(String title, String svgContent, String dotSource) {
        return render(title, /* headerHtml */ null, dotSource, svgBody(svgContent));
    }

    /**
     * Renders a subnet- or instance-aware diagram from pre-rendered SVG.
     * Mirrors {@link #renderSubnetDot} but with the SVG embedded raw.
     *
     * @param title       diagram title
     * @param headerHtml  the HTML produced by {@link SubnetHeader}
     * @param svgContent  pre-rendered SVG (embedded raw, not escaped)
     * @param dotSource   the DOT source code (displayed in the details block)
     * @return HTML markup
     */
    public static String renderSubnetSvg(String title, String headerHtml,
                                         String svgContent, String dotSource) {
        return render(title, headerHtml, dotSource, svgBody(svgContent));
    }

    /**
     * Carries the parts that differ between the DOT-embed and pre-rendered SVG
     * paths: which inlined JS bundle to use, what selector and mount-arg the
     * init script should produce, and what the host {@code <div>} contains.
     * Everything else (CSS, idempotency guard, details/summary block, subnet
     * wrapper class) is identical and lives in {@link #render}.
     */
    private record Body(String inlineJs, String selectorFilter,
                        String mountArg, String hostHtml) {}

    private static Body dotBody(String dotSource) {
        return new Body(
            INLINE_JS,
            "[data-dot]",
            "n.getAttribute('data-dot')",
            "<div class=\"petrinet-diagram-viewer\" data-dot=\"" + escapeHtml(dotSource) + "\"></div>");
    }

    private static Body svgBody(String svgContent) {
        // The viewer code gates on `dotSource == null` to skip its viz path
        // and just wire up pan/zoom + chrome around the existing SVG child.
        return new Body(
            INLINE_STATIC_JS,
            "",
            "null",
            "<div class=\"petrinet-diagram-viewer\">" + svgContent + "</div>");
    }

    private static String render(String title, String headerHtml, String dotSource, Body body) {
        var titleHtml = title != null ? "<h4>%s</h4>\n".formatted(escapeHtml(title)) : "";
        var summaryText = title != null ? "View DOT Source" : "View Source";
        var diagramClass = headerHtml != null ? "petrinet-diagram subnet-diagram" : "petrinet-diagram";
        var headerBlock = headerHtml != null ? headerHtml : "";

        // `chrome:true` asks the viewer to inject its own legend, filter-chip
        // strip, cluster collapse, and fullscreen controls — no placeholders
        // are emitted from the Java side. Idempotency guard keys off
        // `_libpetriViewerInit` so the script only executes once per page.
        return """
            <style>%s</style>
            <script>if(!window._libpetriViewerInit){window._libpetriViewerInit=true;
            %s
            (function(){function mountAll(){if(!window.LibpetriViewer||!window.LibpetriViewer.mount)return;\
            var nodes=document.querySelectorAll('.petrinet-diagram-viewer%s:not([data-libpetri-mounted])');\
            nodes.forEach(function(n){n.setAttribute('data-libpetri-mounted','');\
            try{window.LibpetriViewer.mount(%s,n,{chrome:true});}\
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
                body.inlineJs(),
                body.selectorFilter(),
                body.mountArg(),
                diagramClass,
                titleHtml,
                headerBlock,
                body.hostHtml(),
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
