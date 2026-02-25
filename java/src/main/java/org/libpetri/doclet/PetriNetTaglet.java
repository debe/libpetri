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
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.libpetri.core.NetStructure;
import org.libpetri.core.PetriNet;
import org.libpetri.export.MermaidExporter;

/**
 * Javadoc taglet that auto-generates Petri net diagrams from static fields.
 *
 * <p>This taglet generates Mermaid diagrams by referencing static {@link PetriNet}
 * fields. It uses the {@link MermaidExporter} to create the diagram automatically.
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
 * <h2>Gradle Configuration</h2>
 * <pre>
 * javadoc {
 *     options {
 *         taglets 'org.libpetri.doclet.PetriNetTaglet'
 *         tagletPath configurations.runtimeClasspath.files.toList()
 *     }
 * }
 * </pre>
 *
 * @see MermaidExporter
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

            var mermaid = MermaidExporter.export(petriNet);
            return renderMermaid(petriNet.name(), mermaid);

        } catch (Exception e) {
            return errorHtml("Error generating diagram for '" + reference + "': " + e.getMessage());
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

    /**
     * Attempts to resolve a PetriNet from a static field with the given name.
     *
     * <p>Uses reflection to access the field value. Non-static fields or fields
     * of incompatible types will fail silently.
     *
     * @param clazz the class containing the field
     * @param fieldName the name of the static field to access
     * @return the PetriNet instance, or {@code null} if the field doesn't exist,
     *         isn't accessible, or causes initialization errors
     */
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

    /**
     * Searches for the first static field annotated with {@link NetStructure}
     * that has a {@link PetriNet}-compatible type.
     *
     * <p>Scans all declared fields of the class, including private fields.
     * Returns the first matching field's value; if multiple fields are annotated,
     * only the first encountered is used.
     *
     * @param clazz the class to scan for annotated fields
     * @return the PetriNet from the first matching field, or {@code null} if none found
     */
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

    private String renderMermaid(String title, String mermaidCode) {
        return DiagramRenderer.render(title, mermaidCode);
    }

    private String errorHtml(String message) {
        return """
            <div class="petrinet-error" style="color: #dc3545; border: 1px solid #dc3545; padding: 10px; border-radius: 4px;">
            <strong>@petrinet Error:</strong> %s
            </div>
            """.formatted(DiagramRenderer.escapeHtml(message));
    }
}
