package org.libpetri.doclet;

import com.sun.source.doctree.DocTree;
import com.sun.source.doctree.TextTree;
import com.sun.source.doctree.UnknownBlockTagTree;
import com.sun.source.doctree.UnknownInlineTagTree;
import jdk.javadoc.doclet.Doclet;
import jdk.javadoc.doclet.DocletEnvironment;
import jdk.javadoc.doclet.Taglet;

import javax.lang.model.element.Element;
import javax.lang.model.element.ElementKind;
import javax.lang.model.element.TypeElement;
import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.nio.charset.StandardCharsets;
import java.util.EnumSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.stream.Collectors;

import org.libpetri.core.Instance;
import org.libpetri.core.NetStructure;
import org.libpetri.core.PetriNet;
import org.libpetri.core.SubnetDef;
import org.libpetri.core.SubnetStructure;
import org.libpetri.export.DotExporter;

/**
 * Javadoc taglet that auto-generates Petri net diagrams from static fields.
 *
 * <p>This taglet generates DOT diagrams from static fields whose value is a
 * {@link PetriNet}, {@link SubnetDef}, or {@link Instance}, embeds the DOT
 * source on the page, and hands rendering off to the inlined canonical
 * {@code LibpetriViewer} bundle which converts DOT &rarr; SVG client-side
 * (via an embedded Graphviz WASM build). No external tooling is required on
 * the doc-generation host. The DOT source is also exposed in a collapsible
 * {@code <details>} block beneath each diagram.
 *
 * <h2>Resolution paths</h2>
 * <ol>
 *   <li>{@link PetriNet} — full body diagram (existing behaviour).</li>
 *   <li>{@link SubnetDef} — body diagram with the interface ports highlighted
 *       at the cluster boundary, plus a header showing the subnet name and
 *       declared parameter type.</li>
 *   <li>{@link Instance} — renamed body diagram (already prefix-clustered by
 *       the DOT exporter), plus a header showing the instance prefix, the
 *       originating definition name, and the params summary.</li>
 * </ol>
 *
 * <h2>Auto-discovery</h2>
 * Both {@link NetStructure} and {@link SubnetStructure} fields are discovered
 * when the tag is invoked with an empty reference. The legacy {@code @NetStructure}
 * scan continues to work unchanged.
 *
 * <h2>Usage</h2>
 *
 * <h3>Reference a field in the same class</h3>
 * <pre>{@code
 * /**
 *  * Order processing workflow.
 *  *
 *  * @petrinet STRUCTURE
 *  *{@literal /}
 * public class MyWorkflow {
 *     public static final PetriNet STRUCTURE = ...;
 * }
 * }</pre>
 *
 * <h3>Reference a subnet definition</h3>
 * <pre>{@code
 * /**
 *  * Bounded buffer subnet.
 *  *
 *  * @petrinet BOUNDED_BUFFER
 *  *{@literal /}
 * public class BufferLib {
 *     public static final SubnetDef<Void> BOUNDED_BUFFER = ...;
 * }
 * }</pre>
 *
 * <h3>Inline interface-only citation</h3>
 * <pre>{@code
 * /**
 *  * Wraps a {@subnet BOUNDED_BUFFER} for back-pressure.
 *  *{@literal /}
 * }</pre>
 *
 * @see DotExporter
 * @see PetriNet
 * @see SubnetDef
 * @see Instance
 */
public class PetriNetTaglet implements Taglet {

    private static final String NAME = "petrinet";
    private static final System.Logger LOG = System.getLogger(PetriNetTaglet.class.getName());

    /**
     * Cached {@code dot} availability probe result.
     * <ul>
     *   <li>{@code null} — not yet probed; next call to {@link #tryDotRender}
     *       will attempt to invoke {@code dot}.</li>
     *   <li>{@code Boolean.TRUE} — at least one successful render has
     *       completed; further calls go straight to invocation.</li>
     *   <li>{@code Boolean.FALSE} — the binary is missing or wedged; all
     *       further calls short-circuit to {@link Optional#empty()} so the
     *       taglet falls back to the DOT-embed path.</li>
     * </ul>
     * A non-zero exit code from {@code dot} on a particular diagram does
     * <strong>not</strong> poison the cache — it's likely a malformed input,
     * not a missing binary, so the next diagram still gets a fair attempt.
     */
    private static volatile Boolean dotAvailable;

    /**
     * Memoizes successful renders so the same DOT source isn't forked through
     * {@code dot} twice. A single net field can be referenced from many javadoc
     * pages; without this cache each reference costs another process fork.
     * Empty results are cached too — a per-diagram failure is deterministic
     * for that DOT input, so re-running can't recover.
     */
    private static final ConcurrentHashMap<String, Optional<String>> svgCache = new ConcurrentHashMap<>();

    /**
     * Required public no-arg constructor.
     */
    public PetriNetTaglet() {
    }

    @Override
    public void init(DocletEnvironment env, Doclet doclet) {
        // DocletEnvironment not needed - we use reflection to load Petri net classes
    }

    @Override
    public String getName() {
        return NAME;
    }

    @Override
    public Set<Location> getAllowedLocations() {
        return EnumSet.allOf(Location.class);
    }

    @Override
    public boolean isInlineTag() {
        return true;
    }

    @Override
    public boolean isBlockTag() {
        return true;
    }

    @Override
    public String toString(List<? extends DocTree> tags, Element element) {
        if (tags == null || tags.isEmpty()) {
            return "";
        }

        var result = new StringBuilder();

        for (var tag : tags) {
            var reference = extractContent(tag).trim();
            // Always call generateDiagram - even with blank reference for annotation-based auto-discovery
            result.append(generateDiagram(reference, element));
        }

        return result.toString();
    }

    private String extractContent(DocTree tag) {
        return switch (tag) {
            case UnknownBlockTagTree blockTag ->
                blockTag.getContent().stream()
                    .map(this::extractText)
                    .collect(Collectors.joining());
            case UnknownInlineTagTree inlineTag ->
                inlineTag.getContent().stream()
                    .map(this::extractText)
                    .collect(Collectors.joining());
            default -> tag.toString();
        };
    }

    private String extractText(DocTree tree) {
        return switch (tree) {
            case TextTree text -> text.getBody();
            default -> tree.toString();
        };
    }

    /**
     * Resolves the reference and renders the diagram. Package-private so the
     * sibling {@link SubnetTaglet} can reuse the resolution path without
     * duplicating the reflection plumbing.
     */
    String generateDiagram(String reference, Element contextElement) {
        // Clean up the reference (block tags may have extra content after the field name)
        reference = reference.trim().split("\\s+")[0];
        try {
            var resolved = resolveReference(reference, contextElement);
            if (resolved == null) {
                var errorRef = reference.isBlank()
                        ? "(auto-discovery in " + getEnclosingClassName(contextElement) + ")"
                        : reference;
                return errorHtml("Cannot resolve PetriNet/SubnetDef/Instance: " + errorRef);
            }

            return switch (resolved) {
                case ResolvedNet net -> renderNet(net.value());
                case ResolvedSubnetDef def -> renderSubnetDef(def.value(), false);
                case ResolvedInstance inst -> renderInstance(inst.value());
            };
        } catch (Exception e) {
            return errorHtml("Error generating diagram for '" + reference + "': " + e.getMessage());
        }
    }

    /**
     * Inline-only entry point used by {@link SubnetTaglet} to render an
     * interface-only diagram for a {@link SubnetDef} field. When the resolved
     * reference is not a SubnetDef, falls back to the regular diagram.
     */
    String generateInterfaceOnly(String reference, Element contextElement) {
        reference = reference.trim().split("\\s+")[0];
        try {
            var resolved = resolveReference(reference, contextElement);
            if (resolved == null) {
                return errorHtml("Cannot resolve SubnetDef: " + reference);
            }
            return switch (resolved) {
                case ResolvedSubnetDef def -> renderSubnetDef(def.value(), true);
                case ResolvedNet net -> renderNet(net.value());
                case ResolvedInstance inst -> renderInstance(inst.value());
            };
        } catch (Exception e) {
            return errorHtml("Error generating subnet interface for '" + reference + "': " + e.getMessage());
        }
    }

    // ============================================================
    //  Rendering paths (one per resolved type)
    // ============================================================
    //
    // Hybrid render strategy: try to pre-render the DOT source into SVG via
    // the `dot` command-line tool at doc-generation time; on success embed
    // the SVG raw via DiagramRenderer.renderSvg (slim viewer bundle, no
    // Graphviz WASM on page load); on failure or missing binary, fall back
    // to the client-render path via DiagramRenderer.renderDot which embeds
    // the DOT source as a data-dot attribute and lets the in-page viewer
    // bundle render it via its embedded Graphviz WASM build.

    private String renderNet(PetriNet petriNet) {
        var dot = DotExporter.export(petriNet);
        var svg = tryDotRender(dot);
        return svg.isPresent()
            ? DiagramRenderer.renderSvg(petriNet.name(), svg.get(), dot)
            : DiagramRenderer.renderDot(petriNet.name(), dot);
    }

    private String renderSubnetDef(SubnetDef<?> def, boolean interfaceOnly) {
        var dot = interfaceOnly
            ? SubnetDotExport.interfaceOnly(def)
            : SubnetDotExport.fullBody(def);
        var header = SubnetHeader.forSubnetDef(def, interfaceOnly);
        var title = def.name() + (interfaceOnly ? " (interface)" : "");
        var svg = tryDotRender(dot);
        return svg.isPresent()
            ? DiagramRenderer.renderSubnetSvg(title, header, svg.get(), dot)
            : DiagramRenderer.renderSubnetDot(title, header, dot);
    }

    private String renderInstance(Instance<?> instance) {
        var dot = DotExporter.export(instance.renamedBody());
        var header = SubnetHeader.forInstance(instance);
        var title = instance.def().name() + " :: " + instance.prefix();
        var svg = tryDotRender(dot);
        return svg.isPresent()
            ? DiagramRenderer.renderSubnetSvg(title, header, svg.get(), dot)
            : DiagramRenderer.renderSubnetDot(title, header, dot);
    }

    /**
     * Attempts to pre-render the supplied DOT source into SVG via the
     * {@code dot} command-line tool. Package-private so the sibling test
     * class can drive it directly.
     *
     * <p>Failure semantics:
     * <ul>
     *   <li>If {@code dot} is not on {@code PATH} the {@link ProcessBuilder}
     *       throws an {@link IOException} and the cache is poisoned so all
     *       subsequent calls short-circuit.</li>
     *   <li>If {@code dot} runs but exits non-zero (typically a malformed
     *       diagram) the call returns {@link Optional#empty()} but does
     *       <strong>not</strong> poison the cache.</li>
     *   <li>If {@code dot} wedges past 30 seconds the process is killed and
     *       the cache is poisoned (a wedged binary is functionally missing).</li>
     *   <li>On success the cache flips to {@link Boolean#TRUE} and the SVG
     *       bytes are returned UTF-8 decoded.</li>
     * </ul>
     *
     * @param dot the DOT source code
     * @return the rendered SVG, or {@link Optional#empty()} if {@code dot} is
     *     unavailable or rendering failed
     */
    static Optional<String> tryDotRender(String dot) {
        if (Boolean.FALSE.equals(dotAvailable)) {
            return Optional.empty();
        }
        return svgCache.computeIfAbsent(dot, PetriNetTaglet::doDotRender);
    }

    private static Optional<String> doDotRender(String dot) {
        Process process = null;
        try {
            // Drain stderr separately rather than merging into stdout — `dot`
            // emits warnings (font-not-found, etc.) routinely, and merging
            // would corrupt the SVG bytes. Without a stderr drain at all, the
            // ~64 KB OS pipe fills, dot blocks in write(), waitFor(30s) kills
            // it, and the cache flips to FALSE — silently disabling the
            // pre-render path for the rest of the doc build.
            var pb = new ProcessBuilder("dot", "-Tsvg").redirectErrorStream(false);
            process = pb.start();

            var p = process;
            CompletableFuture<String> outFuture = CompletableFuture.supplyAsync(() -> {
                try {
                    return new String(p.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }
            });
            CompletableFuture<String> errFuture = CompletableFuture.supplyAsync(() -> {
                try {
                    return new String(p.getErrorStream().readAllBytes(), StandardCharsets.UTF_8);
                } catch (IOException e) {
                    return "";
                }
            });

            try (var out = process.getOutputStream()) {
                out.write(dot.getBytes(StandardCharsets.UTF_8));
            }

            if (!process.waitFor(30, TimeUnit.SECONDS)) {
                process.destroyForcibly();
                dotAvailable = false; // a wedged dot is as good as missing
                return Optional.empty();
            }

            if (process.exitValue() != 0) {
                // Per-diagram failure (bad input) — don't poison the cache.
                var stderr = errFuture.getNow("");
                if (!stderr.isBlank()) {
                    LOG.log(System.Logger.Level.DEBUG, "dot exit {0}: {1}",
                            process.exitValue(), stderr);
                }
                return Optional.empty();
            }

            dotAvailable = true;
            var svg = outFuture.get(1, TimeUnit.SECONDS);
            var stderr = errFuture.getNow("");
            if (!stderr.isBlank()) {
                LOG.log(System.Logger.Level.DEBUG, "dot warnings: {0}", stderr);
            }
            return Optional.of(svg);
        } catch (IOException e) {
            // `dot` not on PATH (typical "command not found"). Poison cache.
            dotAvailable = false;
            return Optional.empty();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            if (process != null) process.destroyForcibly();
            return Optional.empty();
        } catch (ExecutionException | TimeoutException e) {
            if (process != null) process.destroyForcibly();
            return Optional.empty();
        }
    }

    /**
     * Resets the cached {@code dot} availability probe. Package-private hook
     * for tests; production code never calls this.
     */
    static void resetDotAvailability() {
        dotAvailable = null;
        svgCache.clear();
    }

    /**
     * Reads the cached {@code dot} availability probe result without
     * triggering a probe. Package-private accessor for tests; production
     * code never calls this.
     *
     * @return {@code null} if not yet probed; {@link Boolean#TRUE} if a
     *     probe succeeded; {@link Boolean#FALSE} if the binary is missing
     *     or wedged
     */
    static Boolean dotAvailableCache() {
        return dotAvailable;
    }

    // ============================================================
    //  Reference resolution (PetriNet / SubnetDef / Instance)
    // ============================================================

    sealed interface Resolved permits ResolvedNet, ResolvedSubnetDef, ResolvedInstance {}
    record ResolvedNet(PetriNet value) implements Resolved {}
    record ResolvedSubnetDef(SubnetDef<?> value) implements Resolved {}
    record ResolvedInstance(Instance<?> value) implements Resolved {}

    private Resolved resolveReference(String reference, Element contextElement) {
        // Determine the class and field name
        String className;
        String fieldName;

        if (reference.contains(".")) {
            // Qualified reference: ClassName.FIELD
            var lastDot = reference.lastIndexOf('.');
            className = reference.substring(0, lastDot);
            fieldName = reference.substring(lastDot + 1);

            // If className is simple, try to resolve it from the context
            if (!className.contains(".")) {
                className = resolveClassName(className, contextElement);
            }
        } else {
            // Simple reference: FIELD - use enclosing class
            fieldName = reference;
            className = getEnclosingClassName(contextElement);
        }

        if (className == null) {
            return null;
        }

        Class<?> clazz;
        try {
            clazz = Class.forName(className);
        } catch (ClassNotFoundException | ExceptionInInitializerError | NoClassDefFoundError e) {
            return null;
        }

        // 1. If explicit reference given, try field by name first.
        if (!reference.isBlank()) {
            var byName = tryFieldByName(clazz, fieldName);
            if (byName != null) {
                return byName;
            }
            LOG.log(System.Logger.Level.DEBUG,
                    "Explicit reference ''{0}'' not found in {1}, falling back to annotation discovery",
                    fieldName, clazz.getName());
        }

        // 2. Look for annotated fields (NetStructure or SubnetStructure).
        return findAnnotatedField(clazz);
    }

    private Resolved tryFieldByName(Class<?> clazz, String fieldName) {
        try {
            var field = clazz.getDeclaredField(fieldName);
            field.setAccessible(true);
            return wrap(field.get(null));
        } catch (NoSuchFieldException | IllegalAccessException |
                 ExceptionInInitializerError | NoClassDefFoundError e) {
            return null;
        }
    }

    private Resolved findAnnotatedField(Class<?> clazz) {
        for (Field field : clazz.getDeclaredFields()) {
            if (!Modifier.isStatic(field.getModifiers())) continue;
            var hasNet = field.isAnnotationPresent(NetStructure.class);
            var hasSubnet = field.isAnnotationPresent(SubnetStructure.class);
            if (!hasNet && !hasSubnet) continue;
            try {
                field.setAccessible(true);
                var resolved = wrap(field.get(null));
                if (resolved != null) return resolved;
            } catch (IllegalAccessException | ExceptionInInitializerError | NoClassDefFoundError e) {
                LOG.log(System.Logger.Level.DEBUG,
                        "Failed to access annotated field {0}.{1}: {2}",
                        clazz.getName(), field.getName(), e.getMessage());
            }
        }
        return null;
    }

    /**
     * Wraps a field value into a {@link Resolved} or returns {@code null} when
     * the value is not one of the supported types.
     */
    private static Resolved wrap(Object value) {
        if (value == null) return null;
        if (value instanceof PetriNet net) return new ResolvedNet(net);
        if (value instanceof SubnetDef<?> def) return new ResolvedSubnetDef(def);
        if (value instanceof Instance<?> inst) return new ResolvedInstance(inst);
        return null;
    }

    private String getEnclosingClassName(Element element) {
        var current = element;
        while (current != null) {
            if (current.getKind() == ElementKind.CLASS ||
                current.getKind() == ElementKind.INTERFACE ||
                current.getKind() == ElementKind.ENUM) {
                return ((TypeElement) current).getQualifiedName().toString();
            }
            current = current.getEnclosingElement();
        }
        return null;
    }

    private String resolveClassName(String simpleName, Element contextElement) {
        // First, check if it's the context class itself
        var enclosing = getEnclosingClassName(contextElement);
        if (enclosing != null && enclosing.endsWith("." + simpleName)) {
            return enclosing;
        }
        if (enclosing != null && enclosing.equals(simpleName)) {
            return enclosing;
        }

        // Try to find the class in the same package
        var current = contextElement;
        while (current != null) {
            if (current.getKind() == ElementKind.PACKAGE) {
                var packageName = current.toString();
                return packageName.isEmpty() ? simpleName : packageName + "." + simpleName;
            }
            current = current.getEnclosingElement();
        }

        return simpleName;
    }

    private String errorHtml(String message) {
        return """
            <div class="petrinet-error" style="color: #dc3545; border: 1px solid #dc3545; padding: 10px; border-radius: 4px;">
            <strong>@petrinet Error:</strong> %s
            </div>
            """.formatted(DiagramRenderer.escapeHtml(message));
    }
}
