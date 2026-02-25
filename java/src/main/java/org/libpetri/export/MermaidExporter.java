package org.libpetri.export;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.libpetri.core.In;
import org.libpetri.core.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Transition;

import static java.util.stream.Collectors.joining;

/**
 * Exports TCPN models to Mermaid flowchart format for visualization.
 *
 * <p><a href="https://mermaid.js.org/">Mermaid</a> is a JavaScript-based diagramming
 * tool that renders markdown-like text into diagrams. This exporter generates
 * Mermaid flowchart syntax that can be:
 * <ul>
 *   <li>Rendered in GitHub/GitLab markdown</li>
 *   <li>Viewed in the <a href="https://mermaid.live/">Mermaid Live Editor</a></li>
 *   <li>Embedded in documentation</li>
 * </ul>
 *
 * <h2>Visual Representation</h2>
 * <ul>
 *   <li><strong>Places:</strong> Stadium-shaped nodes (rounded rectangles)</li>
 *   <li><strong>Transitions:</strong> Rectangular nodes with timing info</li>
 *   <li><strong>Input arcs:</strong> Solid arrows (→)</li>
 *   <li><strong>Output arcs:</strong> Solid arrows (→)</li>
 *   <li><strong>Inhibitor arcs:</strong> Circle-ended arrows (—o)</li>
 *   <li><strong>Read arcs:</strong> Dashed arrows (- - -|read|→)</li>
 *   <li><strong>Reset arcs:</strong> Double-line arrows (= = =|reset|→)</li>
 *   <li><strong>Reset+Output arcs:</strong> Double-line arrows (= = =|reset+out|→) - combined clear and produce</li>
 *   <li><strong>Guarded arcs:</strong> Dashed arrows (- - -|guard|→)</li>
 * </ul>
 *
 * <h2>Styling</h2>
 * <ul>
 *   <li><strong>Start places</strong> (no incoming arcs): Green fill</li>
 *   <li><strong>End places</strong> (no outgoing arcs): Blue fill</li>
 *   <li><strong>Transitions:</strong> Yellow fill</li>
 * </ul>
 *
 * <h2>Usage Example</h2>
 * <pre>{@code
 * var net = PetriNet.builder("MyWorkflow")
 *     .transitions(t1, t2, t3)
 *     .build();
 *
 * // Default configuration
 * String mermaid = MermaidExporter.export(net);
 *
 * // Custom configuration
 * String minimal = MermaidExporter.export(net, Config.minimal());
 * String horizontal = MermaidExporter.export(net, Config.leftToRight());
 * }</pre>
 *
 * <h2>Output Example</h2>
 * <pre>{@code
 * ---
 * config:
 *   layout: elk
 * ---
 * flowchart TB
 *
 *     Start(["Start <String>"])
 *     End(["End <Result>"])
 *
 *     t_Process["Process [0, 5000]ms"]
 *
 *     Start --> t_Process
 *     t_Process --> End
 *
 *     classDef startPlace fill:#d4edda,stroke:#28a745,stroke-width:2px
 *     classDef endPlace fill:#cce5ff,stroke:#004085,stroke-width:2px
 *     class Start startPlace
 *     class End endPlace
 * }</pre>
 *
 * <h2>Live Diagram Example</h2>
 * {@mermaid
 * flowchart TB
 *     Request(["Request"])
 *     t_Process["Process"]
 *     Response(["Response"])
 *     Request --> t_Process
 *     t_Process --> Response
 *     classDef startPlace fill:#d4edda,stroke:#28a745
 *     classDef endPlace fill:#cce5ff,stroke:#004085
 *     class Request startPlace
 *     class Response endPlace
 * }
 *
 * @see <a href="https://mermaid.js.org/syntax/flowchart.html">Mermaid Flowchart Syntax</a>
 */
public final class MermaidExporter {

    private MermaidExporter() {}

    /**
     * Exports a TCPN to Mermaid flowchart with default configuration.
     *
     * @param net the TCPN to export
     * @return Mermaid flowchart syntax
     */
    public static String export(PetriNet net) {
        return export(net, Config.DEFAULT);
    }

    /**
     * Exports a TCPN to Mermaid flowchart with custom configuration.
     *
     * @param net the TCPN to export
     * @param config export configuration
     * @return Mermaid flowchart syntax
     */
    public static String export(PetriNet net, Config config) {
        var places = Places.from(net);

        return Flowchart.of(config.direction)
            .nodes(places.asNodes(config))
            .nodes(transitionNodes(net, config))
            .edges(arcsAsEdges(net))
            .styles(styles(places, net))
            .render();
    }

    // ======================== Node Generation ========================

    private static List<Node> transitionNodes(PetriNet net, Config config) {
        return net.transitions().stream()
            .map(t -> Node.rect(transitionId(t), transitionLabel(t, config)))
            .toList();
    }

    private static String transitionLabel(Transition t, Config config) {
        var parts = Stream.<String>builder().add(t.name());

        if (config.showIntervals) {
            var timing = t.timing();
            var max = timing.hasDeadline()
                ? timing.latest().toMillis() + ""
                : "∞";
            parts.add("[%d, %s]ms".formatted(timing.earliest().toMillis(), max));
        }

        if (config.showPriority && t.priority() != 0) {
            parts.add("prio=" + t.priority());
        }

        return parts.build().collect(joining(" "));
    }

    // ======================== Edge Generation ========================

    /**
     * Recursively generates output edges from Out spec with proper XOR/AND structure.
     * XOR branches get labeled with place name or timeout duration.
     */
    private static List<Edge> outputEdges(String transitionId, Out out, String branchLabel) {
        return switch (out) {
            case Out.Place p -> List.of(
                branchLabel != null
                    ? Edge.weighted(transitionId, p.place().name(), branchLabel)
                    : Edge.solid(transitionId, p.place().name())
            );

            case Out.ForwardInput f -> List.of(
                Edge.dashed(transitionId, f.to().name(),
                    (branchLabel != null ? branchLabel + " " : "") + "⟵" + f.from().name())
            );

            case Out.And and -> and.children().stream()
                .flatMap(c -> outputEdges(transitionId, c, branchLabel).stream())
                .toList();

            case Out.Xor xor -> {
                var edges = new ArrayList<Edge>();
                for (Out child : xor.children()) {
                    String label = inferBranchLabel(child);
                    edges.addAll(outputEdges(transitionId, child, label));
                }
                yield edges;
            }

            case Out.Timeout t -> outputEdges(transitionId, t.child(),
                "⏱" + t.after().toMillis() + "ms");
        };
    }

    /**
     * Infers a branch label from an Out spec for XOR visualization.
     */
    private static String inferBranchLabel(Out out) {
        return switch (out) {
            case Out.Place p -> p.place().name();
            case Out.Timeout t -> "⏱" + t.after().toMillis() + "ms";
            case Out.ForwardInput f -> f.to().name();
            case Out.And _, Out.Xor _ -> null;
        };
    }

    private static List<Edge> arcsAsEdges(PetriNet net) {
        return net.transitions().stream()
            .flatMap(t -> {
                // Collect reset target places for this transition
                var resetPlaces = t.resets().stream()
                    .map(arc -> arc.place().name())
                    .collect(Collectors.toSet());

                // Collect output places from new spec for reset+output detection
                var newOutputPlaces = t.outputSpec() != null
                    ? t.outputSpec().allPlaces().stream().map(p -> p.name()).collect(Collectors.toSet())
                    : java.util.Set.<String>of();

                return Stream.of(
                    // NEW: Input arcs from inputSpecs with cardinality labels
                    t.inputSpecs().stream().map(in -> {
                        var placeName = in.place().name();
                        return switch (in) {
                            case In.One _ -> Edge.solid(placeName, transitionId(t));
                            case In.Exactly e -> Edge.weighted(placeName, transitionId(t), "×" + e.count());
                            case In.All _ -> Edge.weighted(placeName, transitionId(t), "*");
                            case In.AtLeast a -> Edge.weighted(placeName, transitionId(t), "≥" + a.minimum());
                        };
                    }),
                    // Legacy: Input arcs (backward compatibility)
                    t.inputs().values().stream().map(arc -> arc.hasGuard()
                        ? Edge.dashed(arc.place().name(), transitionId(t), "guard")
                        : Edge.solid(arc.place().name(), transitionId(t))),
                    // NEW: Output arcs from outputSpec with XOR/AND structure
                    (t.outputSpec() != null
                        ? outputEdges(transitionId(t), t.outputSpec(), null).stream()
                        : Stream.<Edge>empty()),
                    // Legacy: Output arcs (backward compatibility)
                    t.outputs().stream().map(arc -> {
                        // If output goes to same place as reset, combine into single "reset+out" arc
                        if (resetPlaces.contains(arc.place().name())) {
                            return Edge.resetAndOutput(transitionId(t), arc.place().name());
                        }
                        return Edge.solid(transitionId(t), arc.place().name());
                    }),
                    t.inhibitors().stream().map(arc ->
                        Edge.inhibitor(arc.place().name(), transitionId(t))),
                    t.reads().stream().map(arc ->
                        Edge.dashed(arc.place().name(), transitionId(t), "read")),
                    // Only emit reset arcs that don't have matching output (legacy or new)
                    t.resets().stream()
                        .filter(arc -> t.outputs().stream()
                            .noneMatch(out -> out.place().name().equals(arc.place().name()))
                            && !newOutputPlaces.contains(arc.place().name()))
                        .map(arc -> Edge.reset(transitionId(t), arc.place().name()))
                ).flatMap(s -> s);
            })
            .toList();
    }

    // ======================== Style Generation ========================

    private static List<Style> styles(Places places, PetriNet net) {
        var styles = new ArrayList<Style>();

        var startIds = places.startPlaces();
        var endIds = places.endPlaces();
        var transIds = net.transitions().stream()
            .map(MermaidExporter::transitionId)
            .toList();

        if (!startIds.isEmpty()) {
            styles.add(new Style("startPlace",
                "fill:#d4edda,stroke:#28a745,stroke-width:2px", startIds));
        }
        if (!endIds.isEmpty()) {
            styles.add(new Style("endPlace",
                "fill:#cce5ff,stroke:#004085,stroke-width:2px", endIds));
        }
        if (!transIds.isEmpty()) {
            styles.add(new Style("transition",
                "fill:#fff3cd,stroke:#856404,stroke-width:1px", transIds));
        }

        // XOR transitions get distinctive styling (orange for decision/choice)
        var xorTransIds = net.transitions().stream()
            .filter(t -> t.outputSpec() instanceof Out.Xor)
            .map(MermaidExporter::transitionId)
            .toList();
        if (!xorTransIds.isEmpty()) {
            styles.add(new Style("xorTransition",
                "fill:#ffe6cc,stroke:#d79b00,stroke-width:2px", xorTransIds));
        }

        return styles;
    }

    // ======================== Helpers ========================

    private static String transitionId(Transition t) {
        return "t_" + sanitize(t.name());
    }

    /**
     * Sanitizes a name for use as a Mermaid node ID.
     *
     * <p>Replaces all characters except letters, digits, and underscores with underscores.
     * This is the authoritative sanitization logic - frontend code must use the same algorithm.
     *
     * @param name the name to sanitize
     * @return the sanitized name safe for Mermaid IDs
     */
    public static String sanitize(String name) {
        return name.replaceAll("[^a-zA-Z0-9_]", "_");
    }

    // ======================== Place Analysis ========================

    /**
     * Analyzes places in the net to determine start/end places and types.
     *
     * <p>This is exposed publicly so that debug tooling can access place information
     * without having to re-analyze the net structure.
     */
    public record Places(Map<String, Info> data) {

        /**
         * Information about a place in the net.
         *
         * @param tokenType simple name of the token type
         * @param hasIncoming whether the place has incoming arcs
         * @param hasOutgoing whether the place has outgoing arcs
         */
        public record Info(String tokenType, boolean hasIncoming, boolean hasOutgoing) {
            /** Returns true if this place has no incoming arcs (start place). */
            public boolean isStart() { return !hasIncoming; }
            /** Returns true if this place has no outgoing arcs (end place). */
            public boolean isEnd() { return !hasOutgoing; }
        }

        /**
         * Analyzes a Petri net to extract place information.
         *
         * @param net the Petri net to analyze
         * @return the places analysis
         */
        public static Places from(PetriNet net) {
            record MutableInfo(String tokenType, boolean[] flags) {
                void markIncoming() { flags[0] = true; }
                void markOutgoing() { flags[1] = true; }
                Info toInfo() { return new Info(tokenType, flags[0], flags[1]); }
            }

            var map = new java.util.LinkedHashMap<String, MutableInfo>();

            for (var t : net.transitions()) {
                // NEW: Input places from inputSpecs
                for (var in : t.inputSpecs()) {
                    map.computeIfAbsent(in.place().name(),
                        _ -> new MutableInfo(in.place().tokenType().getSimpleName(),
                            new boolean[2])).markOutgoing();
                }
                // NEW: Output places from outputSpec
                if (t.outputSpec() != null) {
                    for (var place : t.outputSpec().allPlaces()) {
                        map.computeIfAbsent(place.name(),
                            _ -> new MutableInfo(place.tokenType().getSimpleName(),
                                new boolean[2])).markIncoming();
                    }
                }
                // Legacy: Input arcs (backward compatibility)
                for (var arc : t.inputs().values()) {
                    map.computeIfAbsent(arc.place().name(),
                        _ -> new MutableInfo(arc.place().tokenType().getSimpleName(),
                            new boolean[2])).markOutgoing();
                }
                // Legacy: Output arcs (backward compatibility)
                for (var arc : t.outputs()) {
                    map.computeIfAbsent(arc.place().name(),
                        _ -> new MutableInfo(arc.place().tokenType().getSimpleName(),
                            new boolean[2])).markIncoming();
                }
                for (var arc : t.inhibitors()) {
                    map.computeIfAbsent(arc.place().name(),
                        _ -> new MutableInfo(arc.place().tokenType().getSimpleName(),
                            new boolean[2]));
                }
                for (var arc : t.reads()) {
                    map.computeIfAbsent(arc.place().name(),
                        _ -> new MutableInfo(arc.place().tokenType().getSimpleName(),
                            new boolean[2])).markOutgoing();
                }
            }

            return new Places(map.entrySet().stream()
                .collect(Collectors.toMap(
                    Map.Entry::getKey,
                    e -> e.getValue().toInfo(),
                    (a, b) -> a,
                    java.util.LinkedHashMap::new)));
        }

        List<Node> asNodes(Config config) {
            return data.entrySet().stream()
                .map(e -> {
                    var label = config.showTypes && !"Object".equals(e.getValue().tokenType)
                        ? e.getKey() + " #lt;" + e.getValue().tokenType + "#gt;"
                        : e.getKey();
                    return Node.stadium(e.getKey(), label);
                })
                .toList();
        }

        List<String> startPlaces() {
            return data.entrySet().stream()
                .filter(e -> e.getValue().isStart())
                .map(e -> sanitize(e.getKey()))
                .toList();
        }

        List<String> endPlaces() {
            return data.entrySet().stream()
                .filter(e -> e.getValue().isEnd())
                .map(e -> sanitize(e.getKey()))
                .toList();
        }
    }

    // ======================== Mermaid Elements ========================

    /** Represents a node in the flowchart. */
    sealed interface Node {
        String id();
        String label();

        static Node stadium(String id, String label) {
            return new Stadium(sanitize(id), label);
        }
        static Node rect(String id, String label) {
            return new Rect(sanitize(id), label);
        }

        record Stadium(String id, String label) implements Node {}
        record Rect(String id, String label) implements Node {}

        default String render() {
            return switch (this) {
                case Stadium _ -> id() + "([\"" + label() + "\"])";
                case Rect _ -> id() + "[\"" + label() + "\"]";
            };
        }
    }

    /** Represents an edge in the flowchart. */
    sealed interface Edge {
        String from();
        String to();

        static Edge solid(String from, String to) {
            return new Solid(sanitize(from), sanitize(to));
        }
        static Edge dashed(String from, String to, String label) {
            return new Dashed(sanitize(from), sanitize(to), label);
        }
        static Edge inhibitor(String from, String to) {
            return new Inhibitor(sanitize(from), sanitize(to));
        }
        static Edge reset(String from, String to) {
            return new Reset(sanitize(from), sanitize(to));
        }
        static Edge resetAndOutput(String from, String to) {
            return new ResetAndOutput(sanitize(from), sanitize(to));
        }
        /** Arc with weight label (Petri net arc weight notation). */
        static Edge weighted(String from, String to, String weight) {
            return new Weighted(sanitize(from), sanitize(to), weight);
        }

        record Solid(String from, String to) implements Edge {}
        /** Arc with label for arc weight or branch indicator. */
        record Weighted(String from, String to, String weight) implements Edge {}
        record Dashed(String from, String to, String label) implements Edge {}
        record Inhibitor(String from, String to) implements Edge {}
        record Reset(String from, String to) implements Edge {}
        /** Combined reset+output arc - clears place then adds new token. */
        record ResetAndOutput(String from, String to) implements Edge {}

        default String render() {
            return switch (this) {
                case Solid(var f, var t) -> "%s --> %s".formatted(f, t);
                case Weighted(var f, var t, var w) -> "%s -->|%s| %s".formatted(f, w, t);
                case Dashed(var f, var t, var l) -> "%s -.->|%s| %s".formatted(f, l, t);
                case Inhibitor(var f, var t) -> "%s --o %s".formatted(f, t);
                case Reset(var f, var t) -> "%s ==>|reset| %s".formatted(f, t);
                case ResetAndOutput(var f, var t) -> "%s ==>|reset+out| %s".formatted(f, t);
            };
        }
    }

    /** CSS style definition for nodes. */
    record Style(String className, String css, List<String> nodeIds) {
        String renderDef() {
            return "classDef %s %s".formatted(className, css);
        }
        String renderApply() {
            return "class %s %s".formatted(String.join(",", nodeIds), className);
        }
    }

    /** Builder for constructing the complete flowchart. */
    record Flowchart(Direction direction, List<Node> nodes, List<Edge> edges,
                     List<Style> styles) {

        static Builder of(Direction direction) {
            return new Builder(direction);
        }

        static class Builder {
            private final Direction direction;
            private final List<Node> nodes = new ArrayList<>();
            private final List<Edge> edges = new ArrayList<>();
            private final List<Style> styles = new ArrayList<>();

            Builder(Direction direction) {
                this.direction = direction;
            }

            Builder nodes(List<Node> nodes) {
                this.nodes.addAll(nodes);
                return this;
            }

            Builder edges(List<Edge> edges) {
                this.edges.addAll(edges);
                return this;
            }

            Builder styles(List<Style> styles) {
                this.styles.addAll(styles);
                return this;
            }

            String render() {
                return new Flowchart(direction, nodes, edges, styles).render();
            }
        }

        String render() {
            return Stream.of(
                    // YAML front-matter for ELK layout (produces cleaner, more readable diagrams)
                    Stream.of("---"),
                    Stream.of("config:"),
                    Stream.of("  layout: elk"),
                    Stream.of("---"),
                    Stream.of("flowchart " + direction.code),
                    Stream.of(""),
                    nodes.stream().map(n -> "    " + n.render()),
                    Stream.of(""),
                    edges.stream().map(e -> "    " + e.render()),
                    Stream.of(""),
                    styles.isEmpty() ? Stream.<String>empty() : Stream.of("    %% Styles"),
                    styles.stream().map(s -> "    " + s.renderDef()),
                    styles.stream().map(s -> "    " + s.renderApply())
                )
                .flatMap(s -> s)
                .collect(joining("\n"));
        }
    }

    // ======================== Configuration ========================

    /**
     * Flow direction of the diagram.
     */
    public enum Direction {
        /** Top to bottom (default). */
        TB("TB"),
        /** Bottom to top. */
        BT("BT"),
        /** Left to right. */
        LR("LR"),
        /** Right to left. */
        RL("RL");

        final String code;

        Direction(String code) {
            this.code = code;
        }
    }

    /**
     * Configuration options for the Mermaid export.
     *
     * @param direction flow direction of the diagram
     * @param showTypes whether to show token types on places
     * @param showIntervals whether to show firing intervals on transitions
     * @param showPriority whether to show priority on transitions
     */
    public record Config(
        Direction direction,
        boolean showTypes,
        boolean showIntervals,
        boolean showPriority
    ) {
        /** Default configuration: top-to-bottom, show all information. */
        public static final Config DEFAULT = new Config(Direction.TB, true, true, true);

        /** Minimal configuration: no types, intervals, or priorities. */
        public static Config minimal() {
            return new Config(Direction.TB, false, false, false);
        }

        /** Left-to-right layout with all information. */
        public static Config leftToRight() {
            return new Config(Direction.LR, true, true, true);
        }
    }
}
