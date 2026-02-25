package org.libpetri.doclet;

import com.sun.source.doctree.DocTree;
import com.sun.source.doctree.TextTree;
import com.sun.source.doctree.UnknownBlockTagTree;
import com.sun.source.doctree.UnknownInlineTagTree;
import jdk.javadoc.doclet.Doclet;
import jdk.javadoc.doclet.DocletEnvironment;
import jdk.javadoc.doclet.Taglet;

import javax.lang.model.element.Element;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Javadoc taglet for embedding Mermaid diagrams in documentation.
 *
 * <p>This taglet allows you to include Mermaid diagrams directly in your
 * Javadoc comments. The diagrams are rendered as HTML code blocks that
 * can be visualized by Mermaid-aware viewers (GitHub, GitLab, IDE plugins).
 *
 * <h2>Usage</h2>
 *
 * <h3>Block Tag (at end of Javadoc comment)</h3>
 * <pre>{@code
 * /**
 *  * My workflow definition.
 *  *
 *  * @mermaid
 *  * flowchart TB
 *  *     A --> B
 *  *     B --> C
 *  *{@literal /}
 * }</pre>
 *
 * <h3>Inline Tag (within Javadoc text)</h3>
 * <pre>{@code
 * /**
 *  * The workflow is: {@mermaid flowchart LR; A --> B}
 *  *{@literal /}
 * }</pre>
 *
 * <h2>Gradle Configuration</h2>
 * <pre>
 * javadoc {
 *     options {
 *         taglets 'org.libpetri.doclet.MermaidTaglet'
 *         tagletPath configurations.runtimeClasspath.files.toList()
 *     }
 * }
 * </pre>
 *
 * <h2>Rendering</h2>
 * The generated HTML includes a {@code <pre class="mermaid">} block that
 * can be rendered by:
 * <ul>
 *   <li>GitHub/GitLab markdown viewers</li>
 *   <li>IntelliJ IDEA with Mermaid plugin</li>
 *   <li>Browser with Mermaid.js loaded</li>
 * </ul>
 *
 * @see <a href="https://mermaid.js.org/">Mermaid.js</a>
 */
public class MermaidTaglet implements Taglet {

    private static final String NAME = "mermaid";

    /**
     * Required public no-arg constructor.
     */
    public MermaidTaglet() {
    }

    @Override
    public void init(DocletEnvironment env, Doclet doclet) {
        // No initialization needed
    }

    @Override
    public String getName() {
        return NAME;
    }

    @Override
    public Set<Location> getAllowedLocations() {
        // Allow in all documentation locations
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
            var content = extractContent(tag);
            if (content != null && !content.isBlank()) {
                result.append(renderMermaid(content.trim()));
            }
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

    private String renderMermaid(String mermaidCode) {
        return DiagramRenderer.render(mermaidCode);
    }
}
