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
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import org.libpetri.core.NetStructure;
import org.libpetri.core.PetriNet;
import org.libpetri.export.DotExporter;

/**
 * Javadoc taglet that auto-generates Petri net diagrams from static fields.
 *
 * <p>This taglet generates DOT diagrams from {@link PetriNet} fields, converts
 * them to SVG using the {@code dot} command-line tool, and embeds the SVG inline
 * in the Javadoc output. If {@code dot} is not available on the PATH, the DOT
 * source is rendered as a {@code <pre><code>} block instead.
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
 * <h3>Reference a field in another class</h3>
 * <pre>{@code
 * /**
 *  * Uses the order workflow.
 *  *
 *  * @petrinet MyWorkflow.STRUCTURE
 *  *{@literal /}
 * }</pre>
 *
 * <h3>Inline usage</h3>
 * <pre>{@code
 * /**
 *  * The workflow is defined by {@petrinet STRUCTURE}
 *  *{@literal /}
 * }</pre>
 *
 * @see DotExporter
 * @see PetriNet
 */
public class PetriNetTaglet implements Taglet {

    private static final String NAME = "petrinet";
    private static final System.Logger LOG = System.getLogger(PetriNetTaglet.class.getName());

    /**
     * Required public no-arg constructor.
     */
    public PetriNetTaglet() {
    }

    @Override
    public void init(DocletEnvironment env, Doclet doclet) {
        // DocletEnvironment not needed - we use reflection to load PetriNet classes
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

    private String generateDiagram(String reference, Element contextElement) {
        // Clean up the reference (block tags may have extra content after the field name)
        reference = reference.trim().split("\\s+")[0];
        try {
            var petriNet = resolvePetriNet(reference, contextElement);
            if (petriNet == null) {
                var errorRef = reference.isBlank()
                        ? "(auto-discovery in " + getEnclosingClassName(contextElement) + ")"
                        : reference;
                return errorHtml("Cannot resolve PetriNet: " + errorRef);
            }

            var dot = DotExporter.export(petriNet);
            var svg = dotToSvg(dot);
            if (svg != null) {
                return DiagramRenderer.renderSvg(petriNet.name(), svg, dot);
            }
            // Fallback: render DOT as preformatted text
            return DiagramRenderer.renderSvg(petriNet.name(),
                    "<pre><code>" + DiagramRenderer.escapeHtml(dot) + "</code></pre>", dot);

        } catch (Exception e) {
            return errorHtml("Error generating diagram for '" + reference + "': " + e.getMessage());
        }
    }

    /**
     * Converts a DOT string to SVG by invoking the {@code dot} command-line tool.
     *
     * @param dot the DOT source
     * @return SVG string, or {@code null} if {@code dot} is not available
     */
    private String dotToSvg(String dot) {
        try {
            var process = new ProcessBuilder("dot", "-Tsvg")
                    .redirectErrorStream(true)
                    .start();
            process.getOutputStream().write(dot.getBytes(StandardCharsets.UTF_8));
            process.getOutputStream().close();

            var svg = new String(process.getInputStream().readAllBytes(), StandardCharsets.UTF_8);

            if (!process.waitFor(30, TimeUnit.SECONDS)) {
                process.destroyForcibly();
                LOG.log(System.Logger.Level.WARNING, "dot process timed out");
                return null;
            }

            if (process.exitValue() != 0) {
                LOG.log(System.Logger.Level.WARNING, "dot exited with code {0}: {1}",
                        process.exitValue(), svg);
                return null;
            }

            // Strip XML prolog and DOCTYPE — invalid inside HTML5
            int svgStart = svg.indexOf("<svg");
            if (svgStart > 0) svg = svg.substring(svgStart);

            // Strip explicit width/height attributes (e.g. "1942pt") so the SVG
            // scales via viewBox + CSS instead of overriding with fixed pt sizes
            svg = svg.replaceFirst("\\s+width=\"[^\"]*\"", "");
            svg = svg.replaceFirst("\\s+height=\"[^\"]*\"", "");

            return svg;
        } catch (IOException e) {
            LOG.log(System.Logger.Level.DEBUG, "dot not available on PATH: {0}", e.getMessage());
            return null;
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return null;
        }
    }

    private PetriNet resolvePetriNet(String reference, Element contextElement) {
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

        // 1. If explicit reference given, try field by name first
        if (!reference.isBlank()) {
            PetriNet result = tryFieldByName(clazz, fieldName);
            if (result != null) {
                return result;
            }
            // Explicit reference didn't resolve - log before falling back to auto-discovery
            LOG.log(System.Logger.Level.DEBUG,
                    "Explicit reference ''{0}'' not found in {1}, falling back to @NetStructure discovery",
                    fieldName, clazz.getName());
        }

        // 2. Look for @NetStructure annotated field
        return findAnnotatedField(clazz);
    }

    private PetriNet tryFieldByName(Class<?> clazz, String fieldName) {
        try {
            var field = clazz.getDeclaredField(fieldName);
            field.setAccessible(true);
            return (PetriNet) field.get(null);
        } catch (NoSuchFieldException | IllegalAccessException |
                 ExceptionInInitializerError | NoClassDefFoundError e) {
            return null;
        }
    }

    private PetriNet findAnnotatedField(Class<?> clazz) {
        for (Field field : clazz.getDeclaredFields()) {
            if (field.isAnnotationPresent(NetStructure.class)
                    && Modifier.isStatic(field.getModifiers())
                    && PetriNet.class.isAssignableFrom(field.getType())) {
                try {
                    field.setAccessible(true);
                    return (PetriNet) field.get(null);
                } catch (IllegalAccessException | ExceptionInInitializerError | NoClassDefFoundError e) {
                    LOG.log(System.Logger.Level.DEBUG,
                            "Failed to access @NetStructure field {0}.{1}: {2}",
                            clazz.getName(), field.getName(), e.getMessage());
                }
            }
        }
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
