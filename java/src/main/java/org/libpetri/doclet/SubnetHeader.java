package org.libpetri.doclet;

import org.libpetri.core.Instance;
import org.libpetri.core.Interface;
import org.libpetri.core.SubnetDef;

/**
 * HTML-fragment generator for the small "subnet header" badge bar that the
 * {@link DiagramRenderer} layers above subnet diagrams.
 *
 * <p>For a {@link SubnetDef} the header lists the subnet name, the parameter
 * type, and one badge per port and channel — colour-coded by direction
 * ({@code interface-port-input} / {@code -output} / {@code -inout} CSS classes,
 * plus {@code interface-channel} for sync channels).
 *
 * <p>For an {@link Instance} the header lists the instance prefix, the
 * originating definition's name, and the {@code params()} summary.
 */
final class SubnetHeader {

    private SubnetHeader() {}

    /**
     * Builds the header HTML for a {@link SubnetDef} field.
     *
     * @param def           the subnet definition
     * @param interfaceOnly when {@code true}, the header carries the
     *                      "(interface only)" badge so the reader knows the
     *                      body is intentionally omitted
     */
    static String forSubnetDef(SubnetDef<?> def, boolean interfaceOnly) {
        var sb = new StringBuilder();
        sb.append("<div class=\"subnet-header\">\n");
        sb.append("  <div class=\"subnet-header-row\">\n");
        sb.append("    <span class=\"subnet-header-label\">subnet</span>\n");
        sb.append("    <span class=\"subnet-header-name\">")
          .append(DiagramRenderer.escapeHtml(def.name())).append("</span>\n");
        sb.append("    <span class=\"subnet-header-param\">&lt;")
          .append(DiagramRenderer.escapeHtml(def.paramType().getSimpleName())).append("&gt;</span>\n");
        if (interfaceOnly) {
            sb.append("    <span class=\"subnet-header-badge subnet-header-badge-interface\">interface only</span>\n");
        }
        sb.append("  </div>\n");
        sb.append(renderPortChannelBadges(def.iface()));
        sb.append("</div>\n");
        return sb.toString();
    }

    /**
     * Builds the header HTML for an {@link Instance} field.
     */
    static String forInstance(Instance<?> instance) {
        var def = instance.def();
        var sb = new StringBuilder();
        sb.append("<div class=\"subnet-header\">\n");
        sb.append("  <div class=\"subnet-header-row\">\n");
        sb.append("    <span class=\"subnet-header-label\">instance</span>\n");
        sb.append("    <span class=\"subnet-header-name\">")
          .append(DiagramRenderer.escapeHtml(instance.prefix())).append("</span>\n");
        sb.append("    <span class=\"subnet-header-of\">of</span>\n");
        sb.append("    <span class=\"subnet-header-name\">")
          .append(DiagramRenderer.escapeHtml(def.name())).append("</span>\n");
        var params = instance.params();
        if (params != null) {
            sb.append("    <span class=\"subnet-header-params\">params=")
              .append(DiagramRenderer.escapeHtml(String.valueOf(params))).append("</span>\n");
        } else if (!Void.class.equals(def.paramType())) {
            sb.append("    <span class=\"subnet-header-params subnet-header-params-null\">params=null</span>\n");
        }
        sb.append("  </div>\n");
        sb.append(renderPortChannelBadges(def.iface()));
        sb.append("</div>\n");
        return sb.toString();
    }

    /**
     * Renders the per-port and per-channel badge row. Each badge carries a
     * CSS class identifying its kind so the stylesheet can colour-code by
     * direction.
     */
    private static String renderPortChannelBadges(Interface iface) {
        if (iface.ports().isEmpty() && iface.channels().isEmpty()) {
            return "";
        }
        var sb = new StringBuilder();
        sb.append("  <div class=\"subnet-header-badges\">\n");
        for (var port : iface.ports()) {
            var kind = switch (port) {
                case Interface.Port.Input<?> _ -> "input";
                case Interface.Port.Output<?> _ -> "output";
                case Interface.Port.InOut<?> _ -> "inout";
            };
            sb.append("    <span class=\"interface-port-badge interface-port-badge-").append(kind).append("\">")
              .append("<span class=\"badge-direction\">").append(kind).append("</span>")
              .append("<span class=\"badge-name\">").append(DiagramRenderer.escapeHtml(port.name())).append("</span>")
              .append("<span class=\"badge-type\">").append(DiagramRenderer.escapeHtml(port.place().tokenType().getSimpleName())).append("</span>")
              .append("</span>\n");
        }
        for (var channel : iface.channels()) {
            sb.append("    <span class=\"interface-channel-badge\">")
              .append("<span class=\"badge-direction\">channel</span>")
              .append("<span class=\"badge-name\">").append(DiagramRenderer.escapeHtml(channel.name())).append("</span>")
              .append("</span>\n");
        }
        sb.append("  </div>\n");
        return sb.toString();
    }
}
