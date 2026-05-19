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
        var svg = tryRenderPipeline(dot);
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
        var svg = tryRenderPipeline(dot);
        return svg.isPresent()
            ? DiagramRenderer.renderSubnetSvg(title, header, svg.get(), dot)
            : DiagramRenderer.renderSubnetDot(title, header, dot);
    }

    private String renderInstance(Instance<?> instance) {
        var dot = DotExporter.export(instance.renamedBody());
        var header = SubnetHeader.forInstance(instance);
        var title = instance.def().name() + " :: " + instance.prefix();
        var svg = tryRenderPipeline(dot);
        return svg.isPresent()
            ? DiagramRenderer.renderSubnetSvg(title, header, svg.get(), dot)
            : DiagramRenderer.renderSubnetDot(title, header, dot);
    }

    /**
     * Try the C0 Node-CLI pre-render first; on miss fall back to the legacy
     * {@code dot -Tsvg} path. When the env var {@code LIBPETRI_PRERENDER_SCRIPT}
     * is unset (or the CLI fails) we never invoke Node, so doc builds in
     * environments without it pay no penalty.
     */
    static Optional<String> tryRenderPipeline(String dot) {
        var c0 = tryC0Prerender(dot);
        if (c0.isPresent()) return c0;
        return tryDotRender(dot);
    }

    /**
     * Shared subprocess-renderer driver used by both the {@code dot -Tsvg}
     * path ({@link #doDotRender}) and the Node-CLI C0 path
     * ({@link #doC0Prerender}). The two paths differ only in the binary they
     * spawn, the timeout they tolerate, and which static field acts as the
     * cache-poison flag — everything else (stdin pipe-in, concurrent
     * stdout/stderr drain, exit handling) is identical.
     *
     * <p>The dual {@link CompletableFuture} stream drain is load-bearing:
     * without a separate stderr reader, a renderer that prints to stderr
     * (font warnings, ELK info logs) will fill its ~64 KB OS pipe, block in
     * {@code write()}, and the outer {@link Process#waitFor} will kill it
     * after the timeout — silently disabling the renderer for the rest of
     * the doc build via the cache-poison hook.
     *
     * <p>Failure semantics:
     * <ul>
     *   <li>Binary missing → {@link IOException} caught, poison fires,
     *       optionally logged at WARNING (see
     *       {@link SubprocessRendererConfig#logPermanentFailures()}).</li>
     *   <li>Wedged past {@code processTimeoutSeconds} → process killed,
     *       poison fires, optionally logged at WARNING.</li>
     *   <li>Non-zero exit (typically a malformed diagram) → {@link
     *       Optional#empty()} returned, poison does NOT fire (the next
     *       diagram still gets a fair attempt).</li>
     * </ul>
     *
     * @param cfg renderer configuration (command, timeouts, poison hook, label)
     * @param dot DOT source piped to the subprocess on stdin
     * @return the rendered SVG, or {@link Optional#empty()} on any failure
     */
    private static Optional<String> runSubprocessRenderer(
            SubprocessRendererConfig cfg, String dot) {
        Process process = null;
        try {
            var pb = new ProcessBuilder(cfg.command()).redirectErrorStream(false);
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

            if (!process.waitFor(cfg.processTimeoutSeconds(), TimeUnit.SECONDS)) {
                process.destroyForcibly();
                if (cfg.logPermanentFailures()) {
                    LOG.log(System.Logger.Level.WARNING,
                        "{0} wedged past {1}s; falling back to next renderer.",
                        cfg.label(), cfg.processTimeoutSeconds());
                }
                cfg.onPermanentFailure().run();
                return Optional.empty();
            }

            if (process.exitValue() != 0) {
                // Per-diagram failure (bad input) — don't poison.
                var stderr = errFuture.getNow("");
                if (!stderr.isBlank()) {
                    LOG.log(System.Logger.Level.DEBUG, "{0} exit {1}: {2}",
                            cfg.label(), process.exitValue(), stderr);
                }
                return Optional.empty();
            }

            var svg = outFuture.get(cfg.outputDrainTimeoutSeconds(), TimeUnit.SECONDS);
            var stderr = errFuture.getNow("");
            if (!stderr.isBlank()) {
                LOG.log(System.Logger.Level.DEBUG, "{0} warnings: {1}", cfg.label(), stderr);
            }
            return Optional.of(svg);
        } catch (IOException e) {
            // Binary not on PATH or unreadable. Poison.
            if (cfg.logPermanentFailures()) {
                LOG.log(System.Logger.Level.WARNING,
                    "{0} binary unavailable: {1}", cfg.label(), e.getMessage());
            }
            cfg.onPermanentFailure().run();
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
     * Configuration for {@link #runSubprocessRenderer}. Java 25 record keeps
     * the parameter list type-safe and self-documenting.
     *
     * @param command argv passed to {@link ProcessBuilder}
     * @param processTimeoutSeconds hard upper bound on subprocess wall time
     * @param outputDrainTimeoutSeconds extra time (typically 1–2s) to wait
     *     for the stdout drain {@link CompletableFuture} after the process
     *     itself has exited cleanly
     * @param label short human-readable name used in log messages
     * @param onPermanentFailure cache-poison hook; invoked when the binary
     *     is missing or wedges, NOT on per-diagram failures (exit ≠ 0)
     * @param logPermanentFailures when {@code true}, permanent failures log
     *     at WARNING; when {@code false} (the {@code dot} case) the failure
     *     is silent because missing {@code dot} is common and shouldn't
     *     spam every doc build
     */
    private record SubprocessRendererConfig(
            String[] command,
            int processTimeoutSeconds,
            int outputDrainTimeoutSeconds,
            String label,
            Runnable onPermanentFailure,
            boolean logPermanentFailures) {}

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
        var cfg = new SubprocessRendererConfig(
                new String[]{"dot", "-Tsvg"},
                /* processTimeoutSeconds   */ 30,
                /* outputDrainTimeoutSeconds */ 1,
                /* label                   */ "dot",
                /* onPermanentFailure      */ () -> dotAvailable = false,
                /* logPermanentFailures    */ false);
        var svg = runSubprocessRenderer(cfg, dot);
        if (svg.isPresent()) {
            dotAvailable = true;
        }
        return svg;
    }

    /**
     * Resets the cached availability probes for both the {@code dot} and the
     * C0 prerender paths, and clears all memoized SVG outputs.
     * Package-private hook for tests; production code never calls this.
     */
    static void resetDotAvailability() {
        dotAvailable = null;
        c0ScriptResolved = null;
        svgCache.clear();
        c0SvgCache.clear();
    }

    // ============================================================
    //  C0 pre-render via the libpetri Node CLI
    // ============================================================
    //
    // Opt-in via env var LIBPETRI_PRERENDER_SCRIPT (or system property
    // libpetri.prerender.script — preferred, see resolveC0Script). When set,
    // the taglet shells out to `node $LIBPETRI_PRERENDER_SCRIPT`, pipes DOT
    // to stdin, reads SVG from stdout. The Node script runs the same
    // parse → fold → replicate → ELK → writeBack → Graphviz neato (nop=1)
    // pipeline the in-browser viewer uses, so pre-rendered and
    // client-rendered diagrams look identical. ~1s for the 14-subnet
    // Marvin VoiceWorkflowConfig.

    private static final String C0_SCRIPT_ENV = "LIBPETRI_PRERENDER_SCRIPT";
    private static final String C0_SCRIPT_SYSPROP = "libpetri.prerender.script";

    /**
     * Resolved path to the C0 prerender script:
     * <ul>
     *   <li>{@code null} — not yet probed.</li>
     *   <li>non-empty {@link Optional} — script found and at least one
     *       invocation succeeded (or hasn't been tried yet, but env is set).</li>
     *   <li>empty {@link Optional} — env unset or script missing; skip the
     *       Node path for the rest of the doc build.</li>
     * </ul>
     */
    private static volatile Optional<String> c0ScriptResolved;

    private static final ConcurrentHashMap<String, Optional<String>> c0SvgCache = new ConcurrentHashMap<>();

    /**
     * Attempts to pre-render the supplied DOT source via the C0 Node CLI
     * (see {@link #C0_SCRIPT_ENV} / {@link #C0_SCRIPT_SYSPROP}). Cached
     * per-DOT-source to avoid forking Node twice for the same diagram
     * across multiple javadoc pages. Package-private so tests can drive it.
     *
     * <p>Failure semantics (mirror {@link #tryDotRender}, with the C0 twist
     * that the env-var/sysprop opt-in must be honoured first):
     * <ul>
     *   <li>If neither {@link #C0_SCRIPT_ENV} nor {@link #C0_SCRIPT_SYSPROP}
     *       is set, returns {@link Optional#empty()} immediately — Node is
     *       never invoked.</li>
     *   <li>If {@code node} is not on {@code PATH} or the script wedges
     *       past 60 seconds, {@link #c0ScriptResolved} is poisoned and all
     *       further calls short-circuit.</li>
     *   <li>If the script exits non-zero on a particular diagram, returns
     *       {@link Optional#empty()} but does NOT poison.</li>
     * </ul>
     *
     * @param dot the DOT source code
     * @return the rendered SVG, or {@link Optional#empty()} on any failure
     */
    static Optional<String> tryC0Prerender(String dot) {
        var script = resolveC0Script();
        if (script.isEmpty()) return Optional.empty();
        return c0SvgCache.computeIfAbsent(dot, d -> doC0Prerender(script.get(), d));
    }

    /**
     * Resolves the C0 prerender script path from the JVM system property
     * {@link #C0_SCRIPT_SYSPROP} (preferred) or the environment variable
     * {@link #C0_SCRIPT_ENV}. The sysprop is checked first because Gradle
     * daemons capture {@code env} at startup, so a shell-set env var
     * doesn't reach a re-used daemon's forked javadoc JVM — but
     * {@code -Dprop=value} (jFlags) always does. The result is memoized in
     * {@link #c0ScriptResolved} so the filesystem is probed exactly once.
     *
     * @return the absolute path to the script, or {@link Optional#empty()}
     *     when neither source is set or the file is not readable
     */
    private static Optional<String> resolveC0Script() {
        var cached = c0ScriptResolved;
        if (cached != null) return cached;
        var path = System.getProperty(C0_SCRIPT_SYSPROP);
        if (path == null || path.isBlank()) {
            path = System.getenv(C0_SCRIPT_ENV);
        }
        if (path == null || path.isBlank()) {
            c0ScriptResolved = Optional.empty();
            return c0ScriptResolved;
        }
        var file = new java.io.File(path);
        if (!file.isFile() || !file.canRead()) {
            LOG.log(System.Logger.Level.WARNING,
                "C0 prerender script ''{0}'' is not readable; falling back to dot/client.", path);
            c0ScriptResolved = Optional.empty();
            return c0ScriptResolved;
        }
        c0ScriptResolved = Optional.of(path);
        return c0ScriptResolved;
    }

    private static Optional<String> doC0Prerender(String scriptPath, String dot) {
        var cfg = new SubprocessRendererConfig(
                new String[]{"node", scriptPath},
                /* processTimeoutSeconds   */ 60,
                /* outputDrainTimeoutSeconds */ 2,
                /* label                   */ "C0 prerender",
                /* onPermanentFailure      */ () -> c0ScriptResolved = Optional.empty(),
                /* logPermanentFailures    */ true);
        return runSubprocessRenderer(cfg, dot);
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
