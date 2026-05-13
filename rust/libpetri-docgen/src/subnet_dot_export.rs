//! DOT generators for subnet-aware diagrams in rustdoc-embedded SVGs.
//!
//! Mirrors the algorithm of `org.libpetri.doclet.SubnetDotExport` (Java) and
//! `typescript/src/doclet/subnet-dot-export.ts`, ported to Rust.
//!
//! Two flavours:
//! - [`full_body`] — the subnet's complete body, but with its interface-port
//!   places restyled with the `interface-port` category from
//!   `petri-net-styles.json`. A small `subgraph cluster_iface_*` with label
//!   `"interface"` surrounds the port and channel nodes to advertise the
//!   subnet boundary visually.
//! - [`interface_only`] — a tiny diagram of just the port places, the
//!   channel transitions, and a single stub node indicating the body is
//!   omitted. Used by callers that want to advertise the interface without
//!   leaking the body.
//!
//! These functions stay in the docgen crate (rather than living in
//! `libpetri-export`) because they are a presentation concern — the
//! production export pipeline never adds the `interface` cluster.
//! Cluster subgraphs in composed nets are emitted natively by
//! [`libpetri_export::cluster_builder::partition`].

use libpetri_core::interface::{Interface, PortDirection};
use libpetri_core::subnet_def::SubnetDef;
use libpetri_export::dot_exporter::dot_export;
use libpetri_export::mapper::sanitize;
use libpetri_export::styles::{self, NodeVisual};

/// Renders the full body of a [`SubnetDef`] with the interface ports restyled
/// and wrapped in a `cluster_iface_<name>` subgraph. The output is a
/// post-processed version of [`dot_export`]: per-port and per-channel node
/// lines are rewritten so the post-processor swaps in the `interface-port`
/// and `sync-channel` categories. Port and channel ids are then listed inside
/// an extra `subgraph cluster_iface_<name>` block — DOT semantics route a
/// node referenced by id alone into that cluster without re-emitting it.
pub fn full_body<P: 'static>(def: &SubnetDef<P>) -> String {
    let mut dot = dot_export(def.body(), None);
    let port_ids = port_node_ids(def.iface());
    let channel_ids = channel_node_ids(def.iface());

    // Restyle per-id. The renderer emits each node line ending with `];` so
    // a per-id rewrite is sufficient and deterministic.
    for port_id in &port_ids {
        dot = restyle_node(&dot, port_id, &styles::INTERFACE_PORT);
    }
    for ch_id in &channel_ids {
        dot = restyle_node(&dot, ch_id, &styles::SYNC_CHANNEL);
    }

    // Wrap port + channel ids in a header cluster so the doclet's viewer can
    // render the boundary distinctly. Inject before the closing `}` of the
    // digraph.
    if !port_ids.is_empty() || !channel_ids.is_empty() {
        let mut iface = String::new();
        iface.push_str(&format!("    subgraph cluster_iface_{} {{\n", sanitize(def.name())));
        iface.push_str("        label=\"interface\";\n");
        iface.push_str("        style=\"rounded,dashed\";\n");
        iface.push_str("        bgcolor=\"#F0F6FF\";\n");
        iface.push_str("        penwidth=2;\n");
        for id in &port_ids {
            iface.push_str(&format!("        {id};\n"));
        }
        for id in &channel_ids {
            iface.push_str(&format!("        {id};\n"));
        }
        iface.push_str("    }\n");

        if let Some(last_brace) = dot.rfind('}') {
            let mut out = String::with_capacity(dot.len() + iface.len());
            out.push_str(&dot[..last_brace]);
            out.push_str(&iface);
            out.push_str(&dot[last_brace..]);
            dot = out;
        }
    }
    dot
}

/// Renders an interface-only diagram: just the port places, channel
/// transitions, and a single stub node labelled "(internals omitted)" so the
/// reader knows the body has not been drawn.
pub fn interface_only<P: 'static>(def: &SubnetDef<P>) -> String {
    let mut sb = String::new();
    sb.push_str(&format!("digraph {} {{\n", sanitize(def.name())));
    sb.push_str("    rankdir=LR;\n");
    sb.push_str("    nodesep=0.5;\n");
    sb.push_str("    ranksep=0.6;\n");
    sb.push_str(&format!("    fontname=\"{}\";\n", styles::FONT_FAMILY));
    sb.push_str(&format!(
        "    node [fontname=\"{}\", fontsize=12];\n",
        styles::FONT_FAMILY
    ));
    sb.push_str(&format!(
        "    edge [fontname=\"{}\", fontsize=10];\n",
        styles::FONT_FAMILY
    ));
    sb.push('\n');

    let stub_id = format!("stub_{}", sanitize(def.name()));

    // Group ports by direction so the diagram structure is predictable even
    // without the body internals.
    let mut inputs = Vec::new();
    let mut outputs = Vec::new();
    let mut inouts = Vec::new();
    // Sort ports by name for deterministic output (Interface stores them in
    // a HashMap which has unspecified iteration order).
    let mut sorted_ports: Vec<_> = def.iface().ports().collect();
    sorted_ports.sort_by(|a, b| a.name.as_ref().cmp(b.name.as_ref()));
    for port in sorted_ports {
        match port.direction {
            PortDirection::Input => inputs.push(port),
            PortDirection::Output => outputs.push(port),
            PortDirection::InOut => inouts.push(port),
        }
    }

    let mut sorted_channels: Vec<_> = def.iface().channels().collect();
    sorted_channels.sort_by(|a, b| a.name.as_ref().cmp(b.name.as_ref()));

    // Emit port nodes.
    for port in &inputs {
        emit_port_node(&mut sb, port, "input");
    }
    for port in &outputs {
        emit_port_node(&mut sb, port, "output");
    }
    for port in &inouts {
        emit_port_node(&mut sb, port, "inout");
    }

    // Emit channel nodes.
    let sync_style = &styles::SYNC_CHANNEL;
    for ch in &sorted_channels {
        let id = format!("t_{}", sanitize(&ch.transition_name));
        sb.push_str(&format!("    {id} ["));
        sb.push_str(&format!("label=\"⇄ {}\", ", escape_label(&ch.name)));
        sb.push_str(&format!("shape={}, ", sync_style.shape));
        sb.push_str("style=\"filled\", ");
        sb.push_str(&format!("fillcolor=\"{}\", ", sync_style.fill));
        sb.push_str(&format!("color=\"{}\", ", sync_style.stroke));
        sb.push_str(&format!("penwidth={}", trim_double(sync_style.penwidth)));
        sb.push_str("];\n");
    }

    // Emit stub node.
    sb.push_str(&format!("    {stub_id} ["));
    sb.push_str(&format!(
        "label=\"{}\\n(internals omitted)\", ",
        escape_label(def.name())
    ));
    sb.push_str("shape=box, style=\"filled,dashed,rounded\", ");
    sb.push_str("fillcolor=\"#FFFFFF\", color=\"#666666\", penwidth=1, ");
    sb.push_str("fontsize=11");
    sb.push_str("];\n");
    sb.push('\n');

    // Connect inputs -> stub -> outputs; inouts and channels link both ways.
    for port in &inputs {
        sb.push_str(&format!(
            "    {} -> {stub_id} [color=\"#1d4ed8\", arrowhead=normal];\n",
            port_node_id(port.place.name())
        ));
    }
    for port in &outputs {
        sb.push_str(&format!(
            "    {stub_id} -> {} [color=\"#1d4ed8\", arrowhead=normal];\n",
            port_node_id(port.place.name())
        ));
    }
    for port in &inouts {
        sb.push_str(&format!(
            "    {} -> {stub_id} [color=\"#1d4ed8\", arrowhead=normalnormal, dir=both];\n",
            port_node_id(port.place.name())
        ));
    }
    for ch in &sorted_channels {
        let id = format!("t_{}", sanitize(&ch.transition_name));
        sb.push_str(&format!(
            "    {id} -> {stub_id} [color=\"#6d28d9\", arrowhead=normal, style=dashed];\n"
        ));
    }

    sb.push_str("}\n");
    sb
}

/// Passthrough — kept for API stability while callers migrate.
///
/// **Deprecated.** The Rust DOT exporter now emits cluster subgraphs
// ============================================================
//  Helpers
// ============================================================

fn emit_port_node(sb: &mut String, port: &libpetri_core::interface::Port, direction: &str) {
    let style = &styles::INTERFACE_PORT;
    let id = port_node_id(port.place.name());
    sb.push_str(&format!("    {id} ["));
    sb.push_str(&format!("label=\"{}\", ", escape_label(&port.name)));
    sb.push_str(&format!("xlabel=\"{}\", ", escape_label(direction)));
    sb.push_str(&format!("shape={}, ", style.shape));
    sb.push_str(&format!(
        "style=\"filled,{}\", ",
        style.style.unwrap_or("solid")
    ));
    sb.push_str(&format!("fillcolor=\"{}\", ", style.fill));
    sb.push_str(&format!("color=\"{}\", ", style.stroke));
    sb.push_str(&format!("penwidth={}", trim_double(style.penwidth)));
    if let Some(w) = style.width {
        sb.push_str(&format!(", width={}, fixedsize=true", trim_double(w)));
    }
    sb.push_str("];\n");
}

fn port_node_id(place_name: &str) -> String {
    format!("p_{}", sanitize(place_name))
}

fn port_node_ids(iface: &Interface) -> Vec<String> {
    let mut ids: Vec<_> = iface
        .ports()
        .map(|p| port_node_id(p.place.name()))
        .collect();
    ids.sort();
    ids.dedup();
    ids
}

fn channel_node_ids(iface: &Interface) -> Vec<String> {
    let mut ids: Vec<_> = iface
        .channels()
        .map(|c| format!("t_{}", sanitize(&c.transition_name)))
        .collect();
    ids.sort();
    ids.dedup();
    ids
}

/// Rewrites the `fillcolor=`, `color=`, `style=`, and `penwidth=` attributes
/// of the line declaring the given node id so the supplied style takes
/// precedence. Operates as a plain text rewrite: the renderer formats each
/// node line deterministically, so a per-attribute search is reliable.
fn restyle_node(dot: &str, node_id: &str, style: &NodeVisual) -> String {
    // The Rust DOT renderer indents node lines with 2 spaces; Java/TS use 4.
    // Try both so this helper works against either renderer's output.
    let marker = format!("{} [", node_id);
    // Find the start of the line that begins with `<spaces>node_id [`.
    let mut start = None;
    let mut search_from = 0;
    while let Some(rel) = dot[search_from..].find(&marker) {
        let abs = search_from + rel;
        // Walk left to the start of the line.
        let line_start = dot[..abs].rfind('\n').map(|i| i + 1).unwrap_or(0);
        // Verify the bytes between `line_start` and `abs` are all whitespace
        // (so we don't accidentally hit a substring like `j_t_move [`).
        if dot[line_start..abs].chars().all(|c| c == ' ' || c == '\t') {
            start = Some(line_start);
            break;
        }
        search_from = abs + marker.len();
    }
    let start = match start {
        Some(s) => s,
        None => return dot.to_string(),
    };
    let line_end = match dot[start..].find("];") {
        Some(idx) => start + idx + 2,
        None => return dot.to_string(),
    };
    let mut line = dot[start..line_end].to_string();

    // Order matters: keep `fillcolor` before `color` so the substring search
    // for `color="` doesn't accidentally hit `fillcolor="`.
    line = replace_attr(&line, "fillcolor", style.fill);
    line = replace_attr(&line, "color", style.stroke);
    let pw = trim_double(style.penwidth);
    line = replace_attr(&line, "penwidth", &pw);
    if let Some(s) = style.style {
        // Compose with `filled` because the renderer already includes that.
        let composed = format!("\"filled,{s}\"");
        line = replace_attr(&line, "style", &composed);
    }

    let mut out = String::with_capacity(dot.len());
    out.push_str(&dot[..start]);
    out.push_str(&line);
    out.push_str(&dot[line_end..]);
    out
}

/// Replaces the value of a `key=value` pair within a single DOT attribute
/// list. Keeps quoting consistent with the existing form (quoted -> quoted,
/// unquoted -> unquoted).
fn replace_attr(line: &str, key: &str, value: &str) -> String {
    // Match key="..." (quoted) — the key must be preceded by a non-word char
    // (start, comma, or space) so `color=` doesn't match inside `fillcolor=`.
    let quoted_pat = format!("{key}=\"");
    if let Some(q_start) = find_attr_start(line, &quoted_pat) {
        let val_start = q_start + quoted_pat.len();
        if let Some(rel_end) = line[val_start..].find('"') {
            let val_end = val_start + rel_end;
            // strip surrounding quotes from value if it already has them
            let mut v = value;
            if v.len() >= 2 && v.starts_with('"') && v.ends_with('"') {
                v = &v[1..v.len() - 1];
            }
            let mut out = String::with_capacity(line.len() + v.len());
            out.push_str(&line[..val_start]);
            out.push_str(v);
            out.push_str(&line[val_end..]);
            return out;
        }
        return line.to_string();
    }
    // Match key=NN (numeric / unquoted, ends at ',' or ']').
    let unquoted = format!("{key}=");
    if let Some(u_start) = find_attr_start(line, &unquoted) {
        let val_start = u_start + unquoted.len();
        let mut val_end = val_start;
        for (i, c) in line[val_start..].char_indices() {
            if c == ',' || c == ']' {
                val_end = val_start + i;
                break;
            }
            val_end = val_start + i + c.len_utf8();
        }
        let mut out = String::with_capacity(line.len() + value.len());
        out.push_str(&line[..val_start]);
        out.push_str(value);
        out.push_str(&line[val_end..]);
        return out;
    }
    line.to_string()
}

/// Finds the start of a `key=` attribute pattern in `line`, ensuring the
/// match is not a suffix of another attribute name (e.g. `color=` must not
/// match inside `fillcolor=`).
fn find_attr_start(line: &str, pattern: &str) -> Option<usize> {
    let mut from = 0;
    while from <= line.len() {
        let idx = line[from..].find(pattern)?;
        let abs = from + idx;
        if abs == 0 {
            return Some(abs);
        }
        let prev = line.as_bytes()[abs - 1];
        // Word-boundary check: previous char must not be alphanumeric/underscore.
        if !(prev.is_ascii_alphanumeric() || prev == b'_') {
            return Some(abs);
        }
        from = abs + 1;
    }
    None
}

fn trim_double(d: f64) -> String {
    if d == d.trunc() && d.abs() < 1e15 {
        format!("{}", d as i64)
    } else {
        format!("{d}")
    }
}

fn escape_label(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}
