package org.libpetri.export;

import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Transition;
import org.libpetri.export.graph.*;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static java.util.stream.Collectors.joining;

/**
 * Maps a PetriNet definition to a format-agnostic Graph.
 *
 * <p>This is where all the Petri net semantics live. The mapper understands
 * places, transitions, arcs, timing, and priority. It produces a Graph
 * that can be rendered to DOT (or any other format) without Petri net knowledge.
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

        // Edges
        for (var t : net.transitions()) {
            String tid = "t_" + DotExporter.sanitize(t.name());

            // Input arcs from inputSpecs
            for (var in : t.inputSpecs()) {
                String pid = "p_" + DotExporter.sanitize(in.place().name());
                EdgeVisual inputStyle = StyleConstants.edgeStyle(ArcType.INPUT);
                String label = switch (in) {
                    case Arc.In.One _ -> null;
                    case Arc.In.Exactly e -> "\u00d7" + e.count();
                    case Arc.In.All _ -> "*";
                    case Arc.In.AtLeast a -> "\u2265" + a.minimum();
                };
                edges.add(new GraphEdge(
                    pid, tid, label,
                    inputStyle.color(), inputStyle.style(), inputStyle.arrowhead(),
                    inputStyle.penwidth(), ArcType.INPUT, null
                ));
            }

            // Output arcs from outputSpec
            if (t.outputSpec() != null) {
                edges.addAll(outputEdges(tid, t.outputSpec(), null));
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

            // Reset arcs (only those without matching output)
            Set<String> outputPlaceNames = t.outputSpec() != null
                ? t.outputSpec().allPlaces().stream().map(p -> p.name()).collect(Collectors.toSet())
                : Set.of();
            for (var rst : t.resets()) {
                if (!outputPlaceNames.contains(rst.place().name())) {
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
                "fontname", StyleConstants.FONT_FAMILY
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
                : "\u221e";
            parts.add("[%d, %s]ms".formatted(timing.earliest().toMillis(), max));
        }

        if (config.showPriority() && t.priority() != 0) {
            parts.add("prio=" + t.priority());
        }

        return parts.build().collect(joining(" "));
    }

    private static List<GraphEdge> outputEdges(String transitionId, Arc.Out out, String branchLabel) {
        EdgeVisual outStyle = StyleConstants.edgeStyle(ArcType.OUTPUT);

        return switch (out) {
            case Arc.Out.Place p -> {
                String pid = "p_" + DotExporter.sanitize(p.place().name());
                yield List.of(new GraphEdge(
                    transitionId, pid, branchLabel,
                    outStyle.color(), outStyle.style(), outStyle.arrowhead(),
                    outStyle.penwidth(), ArcType.OUTPUT, null
                ));
            }

            case Arc.Out.ForwardInput f -> {
                String pid = "p_" + DotExporter.sanitize(f.to().name());
                String label = (branchLabel != null ? branchLabel + " " : "") + "\u27f5" + f.from().name();
                yield List.of(new GraphEdge(
                    transitionId, pid, label,
                    outStyle.color(), EdgeLineStyle.DASHED, outStyle.arrowhead(),
                    outStyle.penwidth(), ArcType.OUTPUT, null
                ));
            }

            case Arc.Out.And and -> and.children().stream()
                .flatMap(c -> outputEdges(transitionId, c, branchLabel).stream())
                .toList();

            case Arc.Out.Xor xor -> {
                var edges = new ArrayList<GraphEdge>();
                for (var child : xor.children()) {
                    String label = inferBranchLabel(child);
                    edges.addAll(outputEdges(transitionId, child, label));
                }
                yield edges;
            }

            case Arc.Out.Timeout t -> outputEdges(transitionId, t.child(),
                "\u23f1" + t.after().toMillis() + "ms");
        };
    }

    private static String inferBranchLabel(Arc.Out out) {
        return switch (out) {
            case Arc.Out.Place p -> p.place().name();
            case Arc.Out.Timeout t -> "\u23f1" + t.after().toMillis() + "ms";
            case Arc.Out.ForwardInput f -> f.to().name();
            case Arc.Out.And _, Arc.Out.Xor _ -> null;
        };
    }
}
