package org.libpetri.doclet;

import com.sun.source.doctree.DocTree;
import com.sun.source.doctree.TextTree;
import com.sun.source.doctree.UnknownBlockTagTree;
import org.junit.jupiter.api.Test;
import java.util.Optional;
import org.libpetri.core.Arc;
import org.libpetri.core.Instance;
import org.libpetri.core.NetStructure;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.SubnetDef;
import org.libpetri.core.SubnetStructure;
import org.libpetri.core.Transition;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import javax.lang.model.element.ElementKind;
import javax.lang.model.element.ElementVisitor;
import javax.lang.model.element.Name;
import javax.lang.model.element.NestingKind;
import javax.lang.model.element.PackageElement;
import javax.lang.model.element.TypeElement;
import javax.lang.model.element.TypeParameterElement;
import javax.lang.model.type.NoType;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import javax.lang.model.type.TypeVisitor;
import java.lang.annotation.Annotation;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Integration tests for {@link PetriNetTaglet} and {@link SubnetTaglet} —
 * confirms that {@code @petrinet} resolves {@link PetriNet}, {@link SubnetDef},
 * and {@link Instance} static fields, that {@code @SubnetStructure}
 * auto-discovery works, that {@code @subnet} produces an interface-only
 * compact diagram, and that the existing {@code @NetStructure} legacy path
 * is preserved.
 *
 * <p>The tests stub a minimal {@link Element} that carries enough metadata
 * (a {@link TypeElement} enclosing the fixture class) for the taglet's
 * reflection-driven resolver to find the static fields.
 */
class SubnetTagletTest {

    // ============================================================
    //  Fixture: nets, subnets, and instances declared as static fields
    // ============================================================

    record Item(String tag) {}

    static final Place<Item> NET_INPUT = Place.of("NET_INPUT", Item.class);
    static final Place<Item> NET_OUTPUT = Place.of("NET_OUTPUT", Item.class);

    static final Transition NET_TRANSITION = Transition.builder("Process")
        .inputs(Arc.In.one(NET_INPUT))
        .outputs(Arc.Out.place(NET_OUTPUT))
        .build();

    @NetStructure
    public static final PetriNet PLAIN_NET = PetriNet.builder("PlainNet")
        .transition(NET_TRANSITION)
        .build();

    static final Place<Item> SUBNET_IN = Place.of("subnet_in", Item.class);
    static final Place<Item> SUBNET_OUT = Place.of("subnet_out", Item.class);
    static final Transition SUBNET_FORWARD = Transition.builder("forward")
        .inputs(Arc.In.one(SUBNET_IN))
        .outputs(Arc.Out.place(SUBNET_OUT))
        .build();

    @SubnetStructure
    public static final SubnetDef<Void> SAMPLE_SUBNET = SubnetDef.builder("SampleSubnet")
        .transition(SUBNET_FORWARD)
        .inputPort("in_port", SUBNET_IN)
        .outputPort("out_port", SUBNET_OUT)
        .build();

    public static final Instance<Void> SAMPLE_INSTANCE = SAMPLE_SUBNET.instantiate("inst1");

    // Fixture class for the auto-discovery test; @SubnetStructure on the only field.
    public static class AutoDiscoveryFixture {
        // Re-declare distinct places so SAMPLE_SUBNET's identity isn't reused.
        static final Place<Item> AUTO_IN = Place.of("auto_in", Item.class);
        static final Place<Item> AUTO_OUT = Place.of("auto_out", Item.class);
        static final Transition AUTO_T = Transition.builder("auto_forward")
            .inputs(Arc.In.one(AUTO_IN))
            .outputs(Arc.Out.place(AUTO_OUT))
            .build();

        @SubnetStructure
        public static final SubnetDef<Void> AUTO_SUBNET = SubnetDef.builder("AutoSubnet")
            .transition(AUTO_T)
            .inputPort("auto_in", AUTO_IN)
            .outputPort("auto_out", AUTO_OUT)
            .build();
    }

    // Fixture class for cluster-markup smoke test: a composed net with a
    // single instance (so the DOT output carries cluster_*).
    public static class ComposedFixture {
        @NetStructure
        public static final PetriNet COMPOSED = PetriNet.builder("Host")
            .compose(SAMPLE_SUBNET.instantiate("inst1"), Map.of())
            .build();
    }

    // ============================================================
    //  Helpers
    // ============================================================

    private static String enclosingClassNameFor(Class<?> fixture) {
        return fixture.getName();
    }

    /** Builds a block-tag DocTree carrying the supplied reference content. */
    private static List<DocTree> blockTag(String content) {
        var text = new StubTextTree(content);
        var tag = new StubBlockTagTree("petrinet", List.of(text));
        return List.of(tag);
    }

    private static List<DocTree> blockTag(String name, String content) {
        var text = new StubTextTree(content);
        var tag = new StubBlockTagTree(name, List.of(text));
        return List.of(tag);
    }

    private static Element classElement(Class<?> fixture) {
        return new StubTypeElement(fixture.getName());
    }

    // ============================================================
    //  Tests
    // ============================================================

    @Test
    void taglet_resolvesSubnetDefField() {
        // SubnetDef field gets rendered with subnet header (name + interface badges)
        var taglet = new PetriNetTaglet();
        var html = taglet.toString(blockTag("SAMPLE_SUBNET"), classElement(SubnetTagletTest.class));

        assertNotNull(html, "html should not be null");
        // Header is present and shows the subnet name + parameter type
        assertTrue(html.contains("<div class=\"subnet-header\">"),
            "subnet header div should be present:\n" + html);
        assertTrue(html.contains("SampleSubnet"), "subnet name should appear in header:\n" + html);
        // Param type Void appears in the header
        assertTrue(html.contains("&lt;Void&gt;"), "param type Void should appear in header:\n" + html);
        // Port badges with input/output direction (matched as class attribute substring)
        assertTrue(html.contains("interface-port-badge-input\""),
            "input port badge class should be present:\n" + html);
        assertTrue(html.contains("interface-port-badge-output\""),
            "output port badge class should be present:\n" + html);
        // Both port names appear
        assertTrue(html.contains("in_port"), "in_port name should appear:\n" + html);
        assertTrue(html.contains("out_port"), "out_port name should appear:\n" + html);
        // Wrapper class identifies this as a subnet diagram
        assertTrue(html.contains("petrinet-diagram subnet-diagram"),
            "wrapper should carry subnet-diagram class:\n" + html);
    }

    @Test
    void taglet_resolvesInstanceField() {
        var taglet = new PetriNetTaglet();
        var html = taglet.toString(blockTag("SAMPLE_INSTANCE"), classElement(SubnetTagletTest.class));

        assertNotNull(html, "html should not be null");
        // Instance header carries the instance prefix
        assertTrue(html.contains("<div class=\"subnet-header\">"),
            "subnet header div should be present:\n" + html);
        assertTrue(html.contains(">inst1<"), "instance prefix 'inst1' should appear:\n" + html);
        // Header includes "instance" label and the def name
        assertTrue(html.contains(">instance<"), "'instance' label should appear:\n" + html);
        assertTrue(html.contains("SampleSubnet"), "def name should appear:\n" + html);
        assertTrue(html.contains("petrinet-diagram subnet-diagram"),
            "wrapper should carry subnet-diagram class:\n" + html);
    }

    @Test
    void taglet_subnetInlineTag_interfaceOnly() {
        var taglet = new SubnetTaglet();
        var html = taglet.toString(blockTag("subnet", "SAMPLE_SUBNET"),
            classElement(SubnetTagletTest.class));

        assertNotNull(html, "html should not be null");
        // The interface-only flag adds a badge in the header
        assertTrue(html.contains("interface only"),
            "'interface only' badge should appear:\n" + html);
        // The DOT source (in the <details><pre> block) should contain the
        // stub node and NOT the body's "Process" transition node id.
        assertTrue(html.contains("(internals omitted)"),
            "stub label '(internals omitted)' should appear:\n" + html);
        // The body transition id "t_forward" must NOT appear in the
        // interface-only DOT (only port + channel + stub nodes are emitted).
        // We assert against the DOT source carried inside the <details> block.
        var detailsStart = html.indexOf("<details>");
        var detailsEnd = html.indexOf("</details>", detailsStart);
        assertTrue(detailsStart > 0 && detailsEnd > detailsStart, "details block should be present");
        var details = html.substring(detailsStart, detailsEnd);
        // The body's transition is "forward" → "t_forward". It should not appear in the interface-only diagram.
        assertFalse(details.contains("t_forward "),
            "body transition node 't_forward' must be absent from interface-only DOT:\n" + details);
        // Port nodes ARE present.
        assertTrue(details.contains("p_subnet_in"),
            "port place 'p_subnet_in' should appear in interface-only DOT:\n" + details);
        assertTrue(details.contains("p_subnet_out"),
            "port place 'p_subnet_out' should appear in interface-only DOT:\n" + details);
    }

    @Test
    void taglet_subnetStructureAutoDiscovery() {
        var taglet = new PetriNetTaglet();
        // Empty reference => triggers annotation-based auto-discovery.
        var html = taglet.toString(blockTag(""), classElement(AutoDiscoveryFixture.class));

        assertNotNull(html, "html should not be null");
        assertFalse(html.contains("@petrinet Error"),
            "auto-discovery should succeed:\n" + html);
        assertTrue(html.contains("AutoSubnet"),
            "auto-discovered subnet name should appear:\n" + html);
        assertTrue(html.contains("<div class=\"subnet-header\">"),
            "subnet header should appear (proves SubnetStructure was discovered):\n" + html);
    }

    @Test
    void taglet_legacyNetStructure_stillWorks() {
        // Regression guard: a @NetStructure field on a PetriNet must still
        // render as a regular (non-subnet) diagram.
        var taglet = new PetriNetTaglet();
        var html = taglet.toString(blockTag("PLAIN_NET"), classElement(SubnetTagletTest.class));

        assertNotNull(html, "html should not be null");
        assertFalse(html.contains("@petrinet Error"),
            "legacy NetStructure path should not error:\n" + html);
        // Plain net renders WITHOUT the subnet-header div. We assert on the
        // div literal (not the CSS selector that the inlined stylesheet
        // contains) so the inline <style> block doesn't trigger a false hit.
        assertFalse(html.contains("<div class=\"subnet-header\">"),
            "plain PetriNet must not carry subnet-header div:\n" + html);
        assertFalse(html.contains("petrinet-diagram subnet-diagram"),
            "plain PetriNet wrapper must not carry subnet-diagram class:\n" + html);
        // Title is the net name.
        assertTrue(html.contains("PlainNet"),
            "net name should appear:\n" + html);
    }

    @Test
    void taglet_clusterMarkup_present() {
        // A composed host net's DOT must contain a `subgraph cluster_<prefix>` block;
        // this is the input the JS cluster-discovery runtime uses.
        var taglet = new PetriNetTaglet();
        var html = taglet.toString(blockTag("COMPOSED"), classElement(ComposedFixture.class));

        assertNotNull(html, "html should not be null");
        assertFalse(html.contains("@petrinet Error"),
            "composed net should resolve cleanly:\n" + html);
        // The DOT source carries the cluster markup. The HTML escapes '<' but
        // 'subgraph cluster_inst1 {' has no '<' so it survives.
        var detailsStart = html.indexOf("<details>");
        var detailsEnd = html.indexOf("</details>", detailsStart);
        assertTrue(detailsStart > 0 && detailsEnd > detailsStart);
        var details = html.substring(detailsStart, detailsEnd);
        assertTrue(details.contains("subgraph cluster_inst1"),
            "cluster_inst1 block should appear in composed DOT:\n" + details);
    }

    @Test
    void taglet_wiresLibpetriViewer() {
        // The renderer must emit (in BOTH the DOT-embed and pre-rendered SVG
        // paths):
        //   - an init script that calls LibpetriViewer.mount(..., {chrome:true})
        //   - the new idempotency guard (window._libpetriViewerInit)
        // It MUST NOT emit the legacy hand-written IIFE hooks regardless of
        // which path was selected:
        //   - PetriNetDiagrams.toggleFullscreen onclick handler
        //   - empty <aside class="diagram-legend"> placeholder
        //   - empty <div class="diagram-filter-strip"> placeholder
        //   - the old _petriNetDiagramsInit idempotency key
        // The fullscreen button still exists, but it's now created at
        // runtime by the LibpetriViewer chrome — not as static HTML —
        // so we no longer guard against the `btn-fullscreen` string
        // (it legitimately appears inside the inlined JS bundle).
        //
        // Data-dot-specific shape assertions live in dotPath_emitsDataDotHost
        // below (driven directly through DiagramRenderer.renderDot so the
        // contract is covered even on hosts where `dot` IS available and the
        // taglet takes the pre-rendered SVG path).
        var taglet = new PetriNetTaglet();
        var html = taglet.toString(blockTag("PLAIN_NET"), classElement(SubnetTagletTest.class));

        assertNotNull(html, "html should not be null");

        // Generic viewer-wiring assertions — pass for both DOT and SVG paths.
        assertTrue(html.contains("window._libpetriViewerInit"),
            "new idempotency guard should be present:\n" + html);
        assertTrue(html.contains("window.LibpetriViewer"),
            "init script should reference window.LibpetriViewer:\n" + html);
        assertTrue(html.contains("LibpetriViewer.mount("),
            "init script should call LibpetriViewer.mount:\n" + html);
        assertTrue(html.contains("chrome:true"),
            "mount call should request chrome (legend + filter + collapse):\n" + html);
        assertTrue(html.contains("DOMContentLoaded"),
            "init script should defer mounting until DOM ready:\n" + html);

        // Legacy bits MUST be gone regardless of render path.
        assertFalse(html.contains("PetriNetDiagrams.toggleFullscreen"),
            "legacy onclick handler must not appear:\n" + html);
        assertFalse(html.contains("_petriNetDiagramsInit"),
            "legacy idempotency guard must not appear:\n" + html);
        assertFalse(html.contains("<aside class=\"diagram-legend\""),
            "empty legend placeholder must not appear (chrome injects it):\n" + html);
        assertFalse(html.contains("<div class=\"diagram-filter-strip\""),
            "empty filter-strip placeholder must not appear (chrome injects it):\n" + html);
        assertFalse(html.contains("btn-toggle-clusters"),
            "old toggle-clusters control must not appear (chrome owns this):\n" + html);
    }

    @Test
    void dotPath_emitsDataDotHost() {
        // The DOT-embed fallback path must emit a viewer container carrying
        // the DOT source as a `data-dot` attribute. Driven directly through
        // DiagramRenderer.renderDot so the contract is covered regardless of
        // host `dot` availability.
        var dot = "digraph { p_NET_INPUT -> t_Process -> p_NET_OUTPUT }";
        var html = DiagramRenderer.renderDot("PlainNet", dot);

        assertNotNull(html, "html should not be null");
        assertTrue(html.contains("class=\"petrinet-diagram-viewer\" data-dot=\""),
            "viewer container with data-dot attribute should be present:\n" + html);
        // DOT body should be embedded literally (and escaped) inside data-dot.
        assertTrue(html.contains("p_NET_INPUT"),
            "DOT body should be embedded in the data-dot attribute:\n" + html);
    }

    @Test
    void taglet_dataDotEscapesQuotes() {
        // Confirm that any quote characters in the DOT source are HTML-escaped
        // so the data-dot attribute stays well-formed. Driven directly through
        // DiagramRenderer.renderDot so the contract is covered regardless of
        // host `dot` availability (the taglet may take the SVG path if `dot`
        // is on PATH, in which case there is no data-dot attribute at all).
        var dot = "digraph{\"a\"->\"b\"}";
        var html = DiagramRenderer.renderDot("Title", dot);

        var openIdx = html.indexOf("data-dot=\"");
        assertTrue(openIdx > 0, "data-dot attribute should be present");
        var closeIdx = html.indexOf("\">", openIdx + "data-dot=\"".length());
        assertTrue(closeIdx > openIdx,
            "data-dot attribute should terminate with a quote-closing tag:\n" + html);
        var attrValue = html.substring(openIdx + "data-dot=\"".length(), closeIdx);
        // DOT quotes node ids — those must arrive as &quot;, not raw ".
        assertTrue(attrValue.contains("&quot;"),
            "DOT quotes should be escaped to &quot; inside the attribute:\n" + attrValue);
        assertFalse(attrValue.contains("\""),
            "no raw double-quotes should remain inside the attribute value:\n" + attrValue);
    }

    @Test
    void renderSvg_embedsSvgRawWithoutDataDot() {
        var svg = "<svg viewBox='0 0 100 100'><circle r='10' cx='50' cy='50'/></svg>";
        var html = DiagramRenderer.renderSvg("Title", svg, "digraph{a->b}");
        assertTrue(html.contains("<svg viewBox"), "SVG embedded raw:\n" + html);
        assertFalse(html.contains("data-dot="), "no data-dot attribute:\n" + html);
        // The SVG sits immediately inside the viewer host (possibly with
        // whitespace introduced by the text-block formatter).
        assertTrue(html.matches("(?s).*petrinet-diagram-viewer\">\\s*<svg.*"),
            "SVG sits immediately inside the viewer host:\n" + html);
        assertTrue(html.contains("LibpetriViewer.mount(null,"),
            "mount call passes null DOT for pre-rendered path:\n" + html);
        assertTrue(html.contains("View DOT Source"),
            "details block retained:\n" + html);
        assertTrue(html.contains("digraph{a-&gt;b}"),
            "DOT in details is HTML-escaped:\n" + html);
    }

    @Test
    void renderSubnetSvg_includesHeaderAndSubnetClass() {
        var svg = "<svg/>";
        var html = DiagramRenderer.renderSubnetSvg(
            "Title", "<div class=\"subnet-header\">HDR</div>", svg, "digraph{}");
        assertTrue(html.contains("petrinet-diagram subnet-diagram"),
            "wrapper should carry subnet-diagram class:\n" + html);
        assertTrue(html.contains("<div class=\"subnet-header\">HDR</div>"),
            "subnet header HTML should be embedded verbatim:\n" + html);
        assertFalse(html.contains("data-dot="),
            "no data-dot attribute on the SVG path:\n" + html);
    }

    @Test
    void tryDotRender_cachesAvailability() {
        // Reset cache so we're guaranteed to drive a real probe on the
        // first call. After the first call the cache must be set (either
        // Boolean.TRUE on hosts with `dot` on PATH, or Boolean.FALSE on
        // hosts without it — both are valid post-probe states).
        PetriNetTaglet.resetDotAvailability();
        assertNull(PetriNetTaglet.dotAvailableCache(),
            "cache should be null after reset");

        Optional<String> first = PetriNetTaglet.tryDotRender("digraph{}");
        Boolean afterFirst = PetriNetTaglet.dotAvailableCache();
        assertNotNull(afterFirst,
            "cache should be populated after the first probe");

        if (first.isPresent()) {
            assertEquals(Boolean.TRUE, afterFirst,
                "successful render should cache TRUE");
        } else {
            // Either the binary was missing (cache FALSE) or the per-diagram
            // render failed (cache still null). The probe above used a
            // well-formed empty DOT, so the only failure modes are missing
            // binary (FALSE) or a wedged binary (FALSE). Don't allow
            // Boolean.TRUE with empty result — that would be a bug.
            assertNotEquals(Boolean.TRUE, afterFirst,
                "empty result must not be cached as TRUE");
        }

        // A second probe should leave the cache in the same state — neither
        // call should reset or flip it spuriously.
        PetriNetTaglet.tryDotRender("digraph{}");
        assertEquals(afterFirst, PetriNetTaglet.dotAvailableCache(),
            "cache should remain stable across calls");
    }

    // ============================================================
    //  Stub javax.lang.model.element classes
    //  Just enough to satisfy PetriNetTaglet's resolver, which only consults
    //  Element.getKind() + (TypeElement) cast + getQualifiedName().
    // ============================================================

    private static final class StubTypeElement implements TypeElement {
        private final String qualifiedName;

        StubTypeElement(String qualifiedName) {
            this.qualifiedName = qualifiedName;
        }

        @Override public Name getQualifiedName() { return new StubName(qualifiedName); }
        @Override public Name getSimpleName() {
            int dot = qualifiedName.lastIndexOf('.');
            return new StubName(dot < 0 ? qualifiedName : qualifiedName.substring(dot + 1));
        }
        @Override public NestingKind getNestingKind() { return NestingKind.TOP_LEVEL; }
        @Override public TypeMirror getSuperclass() { return new StubNoneType(); }
        @Override public List<? extends TypeMirror> getInterfaces() { return List.of(); }
        @Override public List<? extends TypeParameterElement> getTypeParameters() { return List.of(); }
        @Override public Element getEnclosingElement() {
            int dot = qualifiedName.lastIndexOf('.');
            if (dot < 0) return new StubPackageElement("");
            return new StubPackageElement(qualifiedName.substring(0, dot));
        }
        @Override public List<? extends Element> getEnclosedElements() { return List.of(); }
        @Override public TypeMirror asType() { return new StubNoneType(); }
        @Override public ElementKind getKind() { return ElementKind.CLASS; }
        @Override public java.util.Set<javax.lang.model.element.Modifier> getModifiers() { return java.util.Set.of(); }
        @Override public List<? extends AnnotationMirror> getAnnotationMirrors() { return List.of(); }
        @Override public <A extends Annotation> A getAnnotation(Class<A> annotationType) { return null; }
        @SuppressWarnings("unchecked")
        @Override public <A extends Annotation> A[] getAnnotationsByType(Class<A> annotationType) {
            return (A[]) java.lang.reflect.Array.newInstance(annotationType, 0);
        }
        @Override public <R, P> R accept(ElementVisitor<R, P> v, P p) { return v.visitType(this, p); }
    }

    private static final class StubPackageElement implements PackageElement {
        private final String name;
        StubPackageElement(String name) { this.name = name; }
        @Override public Name getQualifiedName() { return new StubName(name); }
        @Override public Name getSimpleName() {
            int dot = name.lastIndexOf('.');
            return new StubName(dot < 0 ? name : name.substring(dot + 1));
        }
        @Override public boolean isUnnamed() { return name.isEmpty(); }
        @Override public Element getEnclosingElement() { return null; }
        @Override public List<? extends Element> getEnclosedElements() { return List.of(); }
        @Override public TypeMirror asType() { return new StubNoneType(); }
        @Override public ElementKind getKind() { return ElementKind.PACKAGE; }
        @Override public java.util.Set<javax.lang.model.element.Modifier> getModifiers() { return java.util.Set.of(); }
        @Override public List<? extends AnnotationMirror> getAnnotationMirrors() { return List.of(); }
        @Override public <A extends Annotation> A getAnnotation(Class<A> annotationType) { return null; }
        @SuppressWarnings("unchecked")
        @Override public <A extends Annotation> A[] getAnnotationsByType(Class<A> annotationType) {
            return (A[]) java.lang.reflect.Array.newInstance(annotationType, 0);
        }
        @Override public <R, P> R accept(ElementVisitor<R, P> v, P p) { return v.visitPackage(this, p); }
        @Override public String toString() { return name; }
    }

    private static final class StubName implements Name {
        private final String value;
        StubName(String value) { this.value = value; }
        @Override public boolean contentEquals(CharSequence cs) { return value.contentEquals(cs); }
        @Override public int length() { return value.length(); }
        @Override public char charAt(int index) { return value.charAt(index); }
        @Override public CharSequence subSequence(int start, int end) { return value.subSequence(start, end); }
        @Override public String toString() { return value; }
    }

    private static final class StubNoneType implements NoType {
        @Override public TypeKind getKind() { return TypeKind.NONE; }
        @Override public List<? extends AnnotationMirror> getAnnotationMirrors() { return List.of(); }
        @Override public <A extends Annotation> A getAnnotation(Class<A> annotationType) { return null; }
        @SuppressWarnings("unchecked")
        @Override public <A extends Annotation> A[] getAnnotationsByType(Class<A> annotationType) {
            return (A[]) java.lang.reflect.Array.newInstance(annotationType, 0);
        }
        @Override public <R, P> R accept(TypeVisitor<R, P> v, P p) { return v.visitNoType(this, p); }
    }

    /** Minimal {@link UnknownBlockTagTree} stub. */
    private static final class StubBlockTagTree implements UnknownBlockTagTree {
        private final String tagName;
        private final List<? extends DocTree> content;

        StubBlockTagTree(String tagName, List<? extends DocTree> content) {
            this.tagName = tagName;
            this.content = content;
        }

        @Override public String getTagName() { return tagName; }
        @Override public List<? extends DocTree> getContent() { return content; }
        @Override public Kind getKind() { return Kind.UNKNOWN_BLOCK_TAG; }
        @Override public <R, D> R accept(com.sun.source.doctree.DocTreeVisitor<R, D> visitor, D data) {
            return visitor.visitUnknownBlockTag(this, data);
        }
    }

    private static final class StubTextTree implements TextTree {
        private final String body;
        StubTextTree(String body) { this.body = body; }
        @Override public String getBody() { return body; }
        @Override public Kind getKind() { return Kind.TEXT; }
        @Override public <R, D> R accept(com.sun.source.doctree.DocTreeVisitor<R, D> visitor, D data) {
            return visitor.visitText(this, data);
        }
    }
}
