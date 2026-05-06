package org.libpetri.export;

import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Transition;
import org.libpetri.export.graph.*;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static java.util.stream.Collectors.joining;

/**
 * Maps a PetriNet definition to a format-agnostic Graph.
 *
 * <p>Petri net semantics live here. The mapper applies the visualization rules
 * specified in {@code spec/09-export.md} (EXP-012, EXP-013, EXP-014):
 *
 * <ul>
 *   <li>XOR / AND output groups with two or more children become synthetic
 *       diamond junction nodes labelled with a heavy glyph:
 *       {@code ✕} (U+2715) for XOR, {@code ✚} (U+271A) for AND.</li>
 *   <li>Output and reset arcs to the same place collapse into a single edge
 *       styled as the reset-output category and labelled {@code "reset+out"}.</li>
 *   <li>Junction IDs use the form {@code j_<transition>__<kind>_<idx>}, where
 *       {@code idx} is a depth-first pre-order counter starting at 0.</li>
 * </ul>
 */
public final class PetriNetGraphMapper {

    private PetriNetGraphMapper() {}

    /**
     * Maps a PetriNet to a format-agnostic Graph.
     *
     * @param net the Petri net
     * @param config export configuration
     * @return the graph representation
     */
    public static Graph map(PetriNet net, ExportConfig config) {
        var places = PlaceAnalysis.from(net);
        var envNames = config.environmentPlaces();

        var nodes = new ArrayList<GraphNode>();
        var edges = new ArrayList<GraphEdge>();

        // Place nodes
        for (var entry : places.data().entrySet()) {
            String name = entry.getKey();
            String category = places.category(name, envNames);
            NodeVisual style = StyleConstants.nodeStyle(category);
            nodes.add(new GraphNode(
                "p_" + DotExporter.sanitize(name),
                "",
                style.shape(),
                style.fill(),
                style.stroke(),
                style.penwidth(),
                name,
                style.style(),
                style.height(),
                style.width(),
                Map.of("xlabel", name, "fixedsize", "true")
            ));
        }

        // Transition nodes
        for (var t : net.transitions()) {
            NodeVisual style = StyleConstants.TRANSITION;
            nodes.add(new GraphNode(
                "t_" + DotExporter.sanitize(t.name()),
                transitionLabel(t, config),
                style.shape(),
                style.fill(),
                style.stroke(),
                style.penwidth(),
                t.name(),
                style.style(),
                style.height(),
                style.width(),
                null
            ));
        }

        // Edges and junction nodes
        for (var t : net.transitions()) {
            String tid = "t_" + DotExporter.sanitize(t.name());

            Set<String> resetPlaces = t.resets().stream()
                .map(r -> r.place().name())
                .collect(Collectors.toSet());

            // Input arcs from inputSpecs
            for (var in : t.inputSpecs()) {
                String pid = "p_" + DotExporter.sanitize(in.place().name());
                EdgeVisual inputStyle = StyleConstants.edgeStyle(ArcType.INPUT);
                String label = switch (in) {
                    case Arc.In.One _ -> null;
                    case Arc.In.Exactly e -> "×" + e.count();
                    case Arc.In.All _ -> "*";
                    case Arc.In.AtLeast a -> "≥" + a.minimum();
                };
                edges.add(new GraphEdge(
                    pid, tid, label,
                    inputStyle.color(), inputStyle.style(), inputStyle.arrowhead(),
                    inputStyle.penwidth(), ArcType.INPUT, null
                ));
            }

            // Output arcs from outputSpec — emits junction nodes + edges, marks combined places.
            JunctionCtx ctx = new JunctionCtx(
                DotExporter.sanitize(t.name()), resetPlaces, nodes, edges);
            if (t.outputSpec() != null) {
                emitOutput(t.outputSpec(), tid, null, ctx);
            }

            // Inhibitor arcs
            for (var inh : t.inhibitors()) {
                String pid = "p_" + DotExporter.sanitize(inh.place().name());
                EdgeVisual inhStyle = StyleConstants.edgeStyle(ArcType.INHIBITOR);
                edges.add(new GraphEdge(
                    pid, tid, null,
                    inhStyle.color(), inhStyle.style(), inhStyle.arrowhead(),
                    inhStyle.penwidth(), ArcType.INHIBITOR, null
                ));
            }

            // Read arcs
            for (var r : t.reads()) {
                String pid = "p_" + DotExporter.sanitize(r.place().name());
                EdgeVisual readStyle = StyleConstants.edgeStyle(ArcType.READ);
                edges.add(new GraphEdge(
                    pid, tid, "read",
                    readStyle.color(), readStyle.style(), readStyle.arrowhead(),
                    readStyle.penwidth(), ArcType.READ, null
                ));
            }

            // Standalone reset arcs (only those not already combined with an output)
            for (var rst : t.resets()) {
                if (!ctx.combined.contains(rst.place().name())) {
                    String pid = "p_" + DotExporter.sanitize(rst.place().name());
                    EdgeVisual resetStyle = StyleConstants.edgeStyle(ArcType.RESET);
                    edges.add(new GraphEdge(
                        tid, pid, "reset",
                        resetStyle.color(), resetStyle.style(), resetStyle.arrowhead(),
                        resetStyle.penwidth(), ArcType.RESET, null
                    ));
                }
            }
        }

        return new Graph(
            DotExporter.sanitize(net.name()),
            config.direction(),
            nodes,
            edges,
            List.of(),
            Map.of(
                "nodesep", String.valueOf(StyleConstants.NODESEP),
                "ranksep", String.valueOf(StyleConstants.RANKSEP),
                "forcelabels", StyleConstants.FORCE_LABELS,
                "overlap", StyleConstants.OVERLAP,
                "fontname", StyleConstants.FONT_FAMILY,
                "outputorder", StyleConstants.OUTPUT_ORDER
            ),
            Map.of(
                "fontname", StyleConstants.FONT_FAMILY,
                "fontsize", String.valueOf(StyleConstants.NODE_FONT_SIZE)
            ),
            Map.of(
                "fontname", StyleConstants.FONT_FAMILY,
                "fontsize", String.valueOf(StyleConstants.EDGE_FONT_SIZE)
            )
        );
    }

    // ======================== Helpers ========================

    private static String transitionLabel(Transition t, ExportConfig config) {
        var parts = Stream.<String>builder().add(t.name());

        if (config.showIntervals()) {
            var timing = t.timing();
            var max = timing.hasDeadline()
                ? timing.latest().toMillis() + ""
                : "∞";
            parts.add("[%d, %s]ms".formatted(timing.earliest().toMillis(), max));
        }

        if (config.showPriority() && t.priority() != 0) {
            parts.add("prio=" + t.priority());
        }

        return parts.build().collect(joining(" "));
    }

    /**
     * Mutable per-transition state threaded through the recursive Out-tree walk.
     *
     * <p>{@code counter} starts at 0 and increments once per emitted junction
     * (depth-first pre-order). {@code combined} accumulates place names where a
     * reset+output combination short-circuited the standalone reset edge.
     */
    private static final class JunctionCtx {
        final String tSanitized;
        final Set<String> resetPlaces;
        final Set<String> combined = new HashSet<>();
        final List<GraphNode> nodes;
        final List<GraphEdge> edges;
        int counter = 0;

        JunctionCtx(String tSanitized, Set<String> resetPlaces,
                    List<GraphNode> nodes, List<GraphEdge> edges) {
            this.tSanitized = tSanitized;
            this.resetPlaces = resetPlaces;
            this.nodes = nodes;
            this.edges = edges;
        }
    }

    /**
     * Emits output edges for an Out tree, inserting junction nodes for XOR/AND
     * groups with two or more children. Combined reset+output edges replace plain
     * output edges when a leaf place is also in {@code ctx.resetPlaces}.
     *
     * @param out          current Out subtree
     * @param parentId     id of the parent node (transition or junction)
     * @param branchLabel  label to apply to the edge entering this Out (timeout/XOR-branch)
     * @param ctx          per-transition junction context (counter, reset set, accumulators)
     */
    private static void emitOutput(Arc.Out out, String parentId, String branchLabel, JunctionCtx ctx) {
        switch (out) {
            case Arc.Out.Place p -> {
                String pid = "p_" + DotExporter.sanitize(p.place().name());
                pushLeafEdge(parentId, pid, p.place().name(), branchLabel, ctx, false);
            }

            case Arc.Out.ForwardInput f -> {
                String pid = "p_" + DotExporter.sanitize(f.to().name());
                String fwdLabel = (branchLabel != null ? branchLabel + " " : "")
                    + "⟵" + f.from().name();
                pushLeafEdge(parentId, pid, f.to().name(), fwdLabel, ctx, true);
            }

            case Arc.Out.And and -> emitGroup("and", and.children(), parentId, branchLabel, ctx);

            case Arc.Out.Xor xor -> emitGroup("xor", xor.children(), parentId, branchLabel, ctx);

            case Arc.Out.Timeout t -> {
                // Override any inherited branchLabel: the timeout label fully
                // describes this branch (the XOR pre-inference resolves to the
                // same string).
                String timeoutLabel = "⏱" + t.after().toMillis() + "ms";
                emitOutput(t.child(), parentId, timeoutLabel, ctx);
            }
        }
    }

    private static void emitGroup(String kind, List<Arc.Out> children,
                                  String parentId, String branchLabel, JunctionCtx ctx) {
        // Single-child groups collapse: pass through.
        if (children.size() < 2) {
            if (children.size() == 1) {
                emitOutput(children.getFirst(), parentId, branchLabel, ctx);
            }
            return;
        }

        // Insert junction node — diamond gateway with heavy ✕ / ✚ glyph as discriminator.
        int idx = ctx.counter++;
        String junctionId = "j_" + ctx.tSanitized + "__" + kind + "_" + idx;
        String category = kind.equals("xor") ? "xor-junction" : "and-junction";
        NodeVisual jStyle = StyleConstants.nodeStyle(category);
        ctx.nodes.add(new GraphNode(
            junctionId,
            kind.equals("xor") ? "✕" : "✚",
            jStyle.shape(),
            jStyle.fill(),
            jStyle.stroke(),
            jStyle.penwidth(),
            junctionId,
            jStyle.style(),
            jStyle.height(),
            jStyle.width(),
            Map.of("fixedsize", "true", "fontsize", "14")
        ));

        // Edge parent → junction (carries any inherited branch/timeout label).
        EdgeVisual outStyle = StyleConstants.edgeStyle(ArcType.OUTPUT);
        ctx.edges.add(new GraphEdge(
            parentId, junctionId, branchLabel,
            outStyle.color(), outStyle.style(), outStyle.arrowhead(),
            outStyle.penwidth(), ArcType.OUTPUT, null
        ));

        // Recurse children: XOR junction propagates per-branch labels; AND does not.
        for (var child : children) {
            String childLabel = kind.equals("xor") ? inferBranchLabel(child) : null;
            emitOutput(child, junctionId, childLabel, ctx);
        }
    }

    private static void pushLeafEdge(String fromId, String toId, String placeName,
                                     String branchLabel, JunctionCtx ctx, boolean isForwardInput) {
        if (ctx.resetPlaces.contains(placeName)) {
            ctx.combined.add(placeName);
            EdgeVisual ro = StyleConstants.edgeStyle(ArcType.RESET_OUTPUT);
            ctx.edges.add(new GraphEdge(
                fromId, toId, "reset+out",
                ro.color(), ro.style(), ro.arrowhead(),
                ro.penwidth(), ArcType.RESET_OUTPUT, null
            ));
            return;
        }

        EdgeVisual outStyle = StyleConstants.edgeStyle(ArcType.OUTPUT);
        EdgeLineStyle style = isForwardInput ? EdgeLineStyle.DASHED : outStyle.style();
        ctx.edges.add(new GraphEdge(
            fromId, toId, branchLabel,
            outStyle.color(), style, outStyle.arrowhead(),
            outStyle.penwidth(), ArcType.OUTPUT, null
        ));
    }

    private static String inferBranchLabel(Arc.Out out) {
        return switch (out) {
            case Arc.Out.Place p -> p.place().name();
            case Arc.Out.Timeout t -> "⏱" + t.after().toMillis() + "ms";
            case Arc.Out.ForwardInput f -> f.to().name();
            case Arc.Out.And _, Arc.Out.Xor _ -> null;
        };
    }
}
