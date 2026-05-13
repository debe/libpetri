package org.libpetri.doclet;

import org.libpetri.core.Interface;
import org.libpetri.core.SubnetDef;
import org.libpetri.export.DotExporter;
import org.libpetri.export.StyleConstants;
import org.libpetri.export.graph.NodeVisual;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * DOT generators for the subnet-aware diagrams the {@link PetriNetTaglet}
 * draws.
 *
 * <p>Two flavours:
 * <ul>
 *   <li>{@link #fullBody(SubnetDef)} — the subnet's complete body, but with
 *       its interface-port places restyled with the {@code interface-port}
 *       category from {@code petri-net-styles.json} so they read as boundary
 *       elements at a glance. A small {@code subgraph cluster_iface_*} with
 *       label {@code "interface"} surrounds the port places to advertise the
 *       subnet boundary visually.</li>
 *   <li>{@link #interfaceOnly(SubnetDef)} — a tiny diagram of just the port
 *       places, the channel transitions, and a single stub node indicating
 *       the body is omitted. Used by the {@code @subnet} inline tag.</li>
 * </ul>
 *
 * <p>This class stays in the doclet package (rather than living in
 * {@code export/}) because it is a doclet-presentation concern — the
 * production export pipeline never adds the {@code interface} cluster.
 */
final class SubnetDotExport {

    private SubnetDotExport() {}

    /**
     * Renders the full body of a {@link SubnetDef} with the interface ports
     * restyled. The output is a post-processed version of
     * {@link DotExporter#export}: the port-place node attributes are rewritten
     * to use the {@code interface-port} style, channel-transition node
     * attributes to use {@code sync-channel}, and an extra {@code subgraph
     * cluster_iface_<name>} block is appended that lists the port nodes by id
     * — overriding their cluster membership without re-emitting them (DOT
     * semantics: a node referenced inside a subgraph block by id alone is
     * treated as a member of that cluster).
     */
    static String fullBody(SubnetDef<?> def) {
        var dot = DotExporter.export(def.body());
        var portNodeIds = portNodeIds(def.iface());
        var channelNodeIds = channelNodeIds(def.iface());

        // Restyle: rewrite the matched node lines so the post-processor swaps
        // in the interface-port and sync-channel categories. The mapper
        // emits each node as one line ending with `];` so a regex per id is
        // sufficient and deterministic.
        for (var portId : portNodeIds) {
            dot = restyleNode(dot, portId, StyleConstants.INTERFACE_PORT);
        }
        for (var chId : channelNodeIds) {
            dot = restyleNode(dot, chId, StyleConstants.SYNC_CHANNEL);
        }

        // Wrap the port and channel ids in a header cluster so the doclet's
        // viewer can render the boundary distinctly. Done by injecting an
        // extra subgraph block before the closing `}` of the digraph.
        if (!portNodeIds.isEmpty() || !channelNodeIds.isEmpty()) {
            var iface = new StringBuilder();
            iface.append("    subgraph cluster_iface_").append(DotExporter.sanitize(def.name())).append(" {\n");
            iface.append("        label=\"interface\";\n");
            iface.append("        style=\"rounded,dashed\";\n");
            iface.append("        bgcolor=\"#F0F6FF\";\n");
            iface.append("        penwidth=2;\n");
            for (var id : portNodeIds) {
                iface.append("        ").append(id).append(";\n");
            }
            for (var id : channelNodeIds) {
                iface.append("        ").append(id).append(";\n");
            }
            iface.append("    }\n");

            var lastBrace = dot.lastIndexOf('}');
            if (lastBrace > 0) {
                dot = dot.substring(0, lastBrace) + iface + dot.substring(lastBrace);
            }
        }
        return dot;
    }

    /**
     * Renders an interface-only diagram: just the port places + channel
     * transitions + a single stub node labelled "(internals omitted)" so the
     * reader knows the body has not been drawn.
     */
    static String interfaceOnly(SubnetDef<?> def) {
        var sb = new StringBuilder();
        sb.append("digraph ").append(DotExporter.sanitize(def.name())).append(" {\n");
        sb.append("    rankdir=LR;\n");
        sb.append("    nodesep=0.5;\n");
        sb.append("    ranksep=0.6;\n");
        sb.append("    fontname=\"").append(StyleConstants.FONT_FAMILY).append("\";\n");
        sb.append("    node [fontname=\"").append(StyleConstants.FONT_FAMILY).append("\", fontsize=12];\n");
        sb.append("    edge [fontname=\"").append(StyleConstants.FONT_FAMILY).append("\", fontsize=10];\n");
        sb.append("\n");

        var stubId = "stub_" + DotExporter.sanitize(def.name());

        // Group inputs on the left of the stub, outputs on the right; inout
        // and channels appear above. Two helper subgraphs ({rank=same}) keep
        // them aligned.
        var inputs = new LinkedHashSet<Interface.Port>();
        var outputs = new LinkedHashSet<Interface.Port>();
        var inouts = new LinkedHashSet<Interface.Port>();
        for (var port : def.iface().ports()) {
            switch (port) {
                case Interface.Port.Input<?> _ -> inputs.add(port);
                case Interface.Port.Output<?> _ -> outputs.add(port);
                case Interface.Port.InOut<?> _ -> inouts.add(port);
            }
        }

        // Emit port nodes.
        for (var port : inputs) emitPortNode(sb, port, "input");
        for (var port : outputs) emitPortNode(sb, port, "output");
        for (var port : inouts) emitPortNode(sb, port, "inout");

        // Emit channel nodes.
        for (var ch : def.iface().channels()) {
            sb.append("    ").append(channelNodeId(ch)).append(" [");
            sb.append("label=\"⇄ ").append(escapeLabel(ch.name())).append("\", ");
            sb.append("shape=").append(StyleConstants.SYNC_CHANNEL.shape().dotValue()).append(", ");
            sb.append("style=\"filled\", ");
            sb.append("fillcolor=\"").append(StyleConstants.SYNC_CHANNEL.fill()).append("\", ");
            sb.append("color=\"").append(StyleConstants.SYNC_CHANNEL.stroke()).append("\", ");
            sb.append("penwidth=").append(StyleConstants.SYNC_CHANNEL.penwidth());
            sb.append("];\n");
        }

        // Emit stub node.
        sb.append("    ").append(stubId).append(" [");
        sb.append("label=\"").append(escapeLabel(def.name())).append("\\n(internals omitted)\", ");
        sb.append("shape=box, style=\"filled,dashed,rounded\", ");
        sb.append("fillcolor=\"#FFFFFF\", color=\"#666666\", penwidth=1, ");
        sb.append("fontsize=11");
        sb.append("];\n");
        sb.append("\n");

        // Connect inputs -> stub -> outputs; inouts and channels link both ways.
        for (var port : inputs) {
            sb.append("    ").append(portNodeId(port)).append(" -> ").append(stubId)
              .append(" [color=\"#1d4ed8\", arrowhead=normal];\n");
        }
        for (var port : outputs) {
            sb.append("    ").append(stubId).append(" -> ").append(portNodeId(port))
              .append(" [color=\"#1d4ed8\", arrowhead=normal];\n");
        }
        for (var port : inouts) {
            sb.append("    ").append(portNodeId(port)).append(" -> ").append(stubId)
              .append(" [color=\"#1d4ed8\", arrowhead=normalnormal, dir=both];\n");
        }
        for (var ch : def.iface().channels()) {
            sb.append("    ").append(channelNodeId(ch)).append(" -> ").append(stubId)
              .append(" [color=\"#6d28d9\", arrowhead=normal, style=dashed];\n");
        }

        sb.append("}\n");
        return sb.toString();
    }

    // ============================================================
    //  Helpers
    // ============================================================

    private static void emitPortNode(StringBuilder sb, Interface.Port port, String direction) {
        NodeVisual style = StyleConstants.INTERFACE_PORT;
        sb.append("    ").append(portNodeId(port)).append(" [");
        sb.append("label=\"").append(escapeLabel(port.name())).append("\", ");
        sb.append("xlabel=\"").append(escapeLabel(direction)).append(": ")
          .append(escapeLabel(port.place().tokenType().getSimpleName())).append("\", ");
        sb.append("shape=").append(style.shape().dotValue()).append(", ");
        sb.append("style=\"filled,").append(style.style() != null ? style.style() : "solid").append("\", ");
        sb.append("fillcolor=\"").append(style.fill()).append("\", ");
        sb.append("color=\"").append(style.stroke()).append("\", ");
        sb.append("penwidth=").append(style.penwidth());
        if (style.width() != null) sb.append(", width=").append(style.width()).append(", fixedsize=true");
        sb.append("];\n");
    }

    private static String portNodeId(Interface.Port port) {
        return "p_" + DotExporter.sanitize(port.place().name());
    }

    private static String channelNodeId(Interface.Channel ch) {
        return "t_" + DotExporter.sanitize(ch.transition().name());
    }

    private static Set<String> portNodeIds(Interface iface) {
        var ids = new LinkedHashSet<String>();
        for (var port : iface.ports()) ids.add(portNodeId(port));
        return ids;
    }

    private static Set<String> channelNodeIds(Interface iface) {
        var ids = new LinkedHashSet<String>();
        for (var ch : iface.channels()) ids.add(channelNodeId(ch));
        return ids;
    }

    /**
     * Rewrites the {@code fillcolor=}, {@code color=}, {@code style=}, and
     * {@code penwidth=} attributes of the line declaring the given node id so
     * the supplied style takes precedence. Operates as a plain text rewrite:
     * the {@link org.libpetri.export.DotRenderer} formats each node line
     * deterministically, so a per-attribute regex is reliable.
     */
    private static String restyleNode(String dot, String nodeId, NodeVisual style) {
        // The node line begins with: <id> [
        // and ends with: ];
        // Find the line, then surgically swap fillcolor / color / style / penwidth.
        var marker = nodeId + " [";
        int start = dot.indexOf("\n    " + marker);
        if (start < 0) start = dot.indexOf("    " + marker);
        if (start < 0) return dot; // node may live inside a cluster — rare for the body case
        int lineStart = start;
        int lineEnd = dot.indexOf("];", lineStart);
        if (lineEnd < 0) return dot;
        var line = dot.substring(lineStart, lineEnd + 2);

        var rewrites = new LinkedHashMap<String, String>();
        rewrites.put("fillcolor", style.fill());
        rewrites.put("color", style.stroke());
        rewrites.put("penwidth", trimDouble(style.penwidth()));
        if (style.style() != null) {
            // Compose with `filled` because the renderer already includes that.
            rewrites.put("style", "\"filled," + style.style() + "\"");
        }

        for (var entry : rewrites.entrySet()) {
            line = replaceAttr(line, entry.getKey(), entry.getValue());
        }

        return dot.substring(0, lineStart) + line + dot.substring(lineEnd + 2);
    }

    /**
     * Replaces the value of a {@code key=value} pair within a single DOT
     * attribute list. Quotes the value when it isn't already quoted.
     */
    private static String replaceAttr(String line, String key, String value) {
        // Match key="..." (quoted) and key=N (numeric / unquoted)
        var quotedPat = key + "=\"";
        int qStart = line.indexOf(quotedPat);
        if (qStart >= 0) {
            int valStart = qStart + quotedPat.length();
            int valEnd = line.indexOf('"', valStart);
            if (valEnd < 0) return line;
            // strip surrounding quotes from value if it already has them
            var v = value;
            if (v.startsWith("\"") && v.endsWith("\"") && v.length() >= 2) {
                v = v.substring(1, v.length() - 1);
            }
            return line.substring(0, valStart) + v + line.substring(valEnd);
        }
        // Match key=NN or key=NN, or key=NN]
        var unquoted = key + "=";
        int uStart = line.indexOf(unquoted);
        if (uStart < 0) return line;
        int valStart = uStart + unquoted.length();
        int valEnd = valStart;
        while (valEnd < line.length()) {
            var c = line.charAt(valEnd);
            if (c == ',' || c == ']') break;
            valEnd++;
        }
        // numeric replacement keeps it unquoted
        return line.substring(0, valStart) + value + line.substring(valEnd);
    }

    private static String trimDouble(double d) {
        if (d == (long) d) return String.valueOf((long) d);
        return String.valueOf(d);
    }

    private static String escapeLabel(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"");
    }
}
