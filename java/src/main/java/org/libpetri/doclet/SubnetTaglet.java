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

import org.libpetri.core.SubnetDef;

/**
 * Inline javadoc taglet that renders a compact, interface-only diagram of a
 * {@link SubnetDef} field — for citing a subnet without expanding its body.
 *
 * <p>The rendered diagram is a small box showing the subnet's port labels
 * (input/output/inout colour-coded), the channel labels, and the parameter
 * type. The body internals are intentionally omitted; cite a subnet's
 * full body via the regular {@code @petrinet} block tag.
 *
 * <h2>Usage</h2>
 * <pre>{@code
 * /**
 *  * The producer pipeline plugs into a {@subnet BoundedBuffer} for back-pressure.
 *  *{@literal /}
 * }</pre>
 *
 * @see PetriNetTaglet
 * @see SubnetDef
 */
public class SubnetTaglet implements Taglet {

    private static final String NAME = "subnet";

    private final PetriNetTaglet delegate = new PetriNetTaglet();

    /** Required public no-arg constructor. */
    public SubnetTaglet() {
    }

    @Override
    public void init(DocletEnvironment env, Doclet doclet) {
        delegate.init(env, doclet);
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
            result.append(delegate.generateInterfaceOnly(reference, element));
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
}
