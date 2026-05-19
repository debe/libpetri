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

    private String renderNet(PetriNet petriNet) {
        return DiagramRenderer.renderDot(petriNet.name(), DotExporter.export(petriNet));
    }

    private String renderSubnetDef(SubnetDef<?> def, boolean interfaceOnly) {
        var dot = interfaceOnly
            ? SubnetDotExport.interfaceOnly(def)
            : SubnetDotExport.fullBody(def);
        var header = SubnetHeader.forSubnetDef(def, interfaceOnly);
        var title = def.name() + (interfaceOnly ? " (interface)" : "");
        return DiagramRenderer.renderSubnetDot(title, header, dot);
    }

    private String renderInstance(Instance<?> instance) {
        var dot = DotExporter.export(instance.renamedBody());
        var header = SubnetHeader.forInstance(instance);
        var title = instance.def().name() + " :: " + instance.prefix();
        return DiagramRenderer.renderSubnetDot(title, header, dot);
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
