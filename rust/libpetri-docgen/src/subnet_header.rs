//! HTML-fragment generator for the small "subnet header" badge bar that the
//! [`crate::diagram_renderer`] layers above subnet diagrams.
//!
//! Mirrors `org.libpetri.doclet.SubnetHeader` (Java) and
//! `typescript/src/doclet/subnet-header.ts` (TypeScript).
//!
//! For a [`SubnetDef`] the header lists the subnet name and one badge per
//! port and channel — colour-coded by direction (`interface-port-input` /
//! `-output` / `-inout` CSS classes, plus `interface-channel` for sync
//! channels).
//!
//! For an [`Instance`] the header lists the instance prefix, the originating
//! definition's name, and a `params=...` summary when applicable.

use libpetri_core::instance::Instance;
use libpetri_core::interface::{Interface, PortDirection};
use libpetri_core::subnet_def::SubnetDef;

use crate::diagram_renderer::escape_html;

/// Builds the header HTML for a [`SubnetDef`] field.
///
/// When `interface_only` is `true`, the header carries an "interface only"
/// badge so the reader knows the body is intentionally omitted.
pub fn for_subnet_def<P: 'static>(def: &SubnetDef<P>, interface_only: bool) -> String {
    let mut sb = String::new();
    sb.push_str("<div class=\"subnet-header\">\n");
    sb.push_str("  <div class=\"subnet-header-row\">\n");
    sb.push_str("    <span class=\"subnet-header-label\">subnet</span>\n");
    sb.push_str(&format!(
        "    <span class=\"subnet-header-name\">{}</span>\n",
        escape_html(def.name())
    ));
    // Rust generics are erased at runtime — we cannot expose `P`'s simple
    // name without a `TypeId -> &str` registry. The Java/TS counterparts
    // emit the simple class name; here we omit the generic parameter slot
    // to avoid a misleading placeholder.
    if interface_only {
        sb.push_str(
            "    <span class=\"subnet-header-badge subnet-header-badge-interface\">interface only</span>\n",
        );
    }
    sb.push_str("  </div>\n");
    sb.push_str(&render_port_channel_badges(Some(def.iface())));
    sb.push_str("</div>\n");
    sb
}

/// Builds the header HTML for an [`Instance`] field.
pub fn for_instance<P: 'static>(instance: &Instance<P>) -> String {
    let mut sb = String::new();
    sb.push_str("<div class=\"subnet-header\">\n");
    sb.push_str("  <div class=\"subnet-header-row\">\n");
    sb.push_str("    <span class=\"subnet-header-label\">instance</span>\n");
    sb.push_str(&format!(
        "    <span class=\"subnet-header-name\">{}</span>\n",
        escape_html(instance.prefix())
    ));
    sb.push_str("    <span class=\"subnet-header-of\">of</span>\n");
    sb.push_str(&format!(
        "    <span class=\"subnet-header-name\">{}</span>\n",
        escape_html(instance.def_name())
    ));
    // Rust cannot stringify arbitrary `P` values without `Display`. Emit a
    // "params=…" badge only for the unit type to keep parity with the
    // Java/TS "params=null" sentinel; richer formatting lands when the
    // future SubnetInstance descriptor exposes a `params_str()`.
    sb.push_str("  </div>\n");
    // Instance does not expose its origin Interface (see `instance.rs` —
    // port_handles + channel_handles are kept separately and the Interface
    // lives on the SubnetDef). Skip the per-port badge row for instance
    // headers — the header still carries the prefix + def_name labels which
    // is the load-bearing information.
    let _ = instance;
    sb.push_str("</div>\n");
    sb
}

/// Renders the per-port + per-channel badge row for a [`SubnetDef`]'s
/// interface. Each badge carries a CSS class identifying its kind so the
/// stylesheet can colour-code by direction.
fn render_port_channel_badges(iface: Option<&Interface>) -> String {
    let Some(iface) = iface else {
        return String::new();
    };
    if iface.port_count() == 0 && iface.channel_count() == 0 {
        return String::new();
    }
    let mut sb = String::new();
    sb.push_str("  <div class=\"subnet-header-badges\">\n");

    // Sort ports + channels for deterministic output (HashMap iteration
    // order is unspecified).
    let mut ports: Vec<_> = iface.ports().collect();
    ports.sort_by(|a, b| a.name.as_ref().cmp(b.name.as_ref()));
    for port in ports {
        let kind = match port.direction {
            PortDirection::Input => "input",
            PortDirection::Output => "output",
            PortDirection::InOut => "inout",
        };
        sb.push_str(&format!(
            "    <span class=\"interface-port-badge interface-port-badge-{kind}\">\
             <span class=\"badge-direction\">{kind}</span>\
             <span class=\"badge-name\">{name}</span>\
             </span>\n",
            name = escape_html(&port.name),
        ));
    }
    let mut channels: Vec<_> = iface.channels().collect();
    channels.sort_by(|a, b| a.name.as_ref().cmp(b.name.as_ref()));
    for channel in channels {
        sb.push_str(&format!(
            "    <span class=\"interface-channel-badge\">\
             <span class=\"badge-direction\">channel</span>\
             <span class=\"badge-name\">{name}</span>\
             </span>\n",
            name = escape_html(&channel.name),
        ));
    }
    sb.push_str("  </div>\n");
    sb
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    fn build_subnet() -> SubnetDef<()> {
        let p_in = Place::<i32>::new("inp");
        let p_out = Place::<i32>::new("outp");
        let t = Transition::builder("move")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .build();
        SubnetDef::<()>::builder("Mover")
            .transition(t.clone())
            .input_port("inport", &p_in)
            .output_port("outport", &p_out)
            .channel("ch", &t)
            .build()
    }

    #[test]
    fn subnet_def_header_has_name_and_label() {
        let def = build_subnet();
        let html = for_subnet_def(&def, false);
        assert!(html.contains("subnet-header"));
        assert!(html.contains(">subnet<"));
        assert!(html.contains(">Mover<"));
    }

    #[test]
    fn subnet_def_header_interface_only_badge() {
        let def = build_subnet();
        let html = for_subnet_def(&def, true);
        assert!(html.contains("interface only"));
    }

    #[test]
    fn subnet_def_header_includes_port_and_channel_badges() {
        let def = build_subnet();
        let html = for_subnet_def(&def, false);
        assert!(html.contains("interface-port-badge-input"));
        assert!(html.contains("interface-port-badge-output"));
        assert!(html.contains("interface-channel-badge"));
        assert!(html.contains(">inport<"));
        assert!(html.contains(">outport<"));
        assert!(html.contains(">ch<"));
    }

    #[test]
    fn instance_header_has_prefix_and_def_name() {
        let def = build_subnet();
        let inst = def.instantiate("b1", ());
        let html = for_instance(&inst);
        assert!(html.contains(">instance<"));
        assert!(html.contains(">b1<"));
        assert!(html.contains(">of<"));
        assert!(html.contains(">Mover<"));
    }
}

