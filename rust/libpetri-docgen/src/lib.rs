//! Build-script helper for embedding Petri net diagrams in rustdoc.
//!
//! This crate is intended as a **build-dependency**. It takes a [`PetriNet`]
//! definition, exports it to DOT via [`dot_export`], wraps the DOT source in
//! a self-contained HTML page (CSS + the canonical `LibpetriViewer` IIFE +
//! the DOT in a `data-dot` attribute), and writes the result to `OUT_DIR` so
//! it can be embedded in rustdoc with [`include_str!`].
//!
//! The bundled viewer renders DOT → SVG client-side via an embedded Graphviz
//! WASM build, so the doc-generation host does **not** need any external
//! tooling installed.
//!
//! # Quick Start
//!
//! **Cargo.toml:**
//! ```toml
//! [build-dependencies]
//! libpetri-docgen = "1.2"
//! ```
//!
//! **build.rs:**
//! ```rust,no_run
//! use libpetri_docgen::*;
//!
//! fn main() {
//!     let p1 = Place::<i32>::new("input");
//!     let p2 = Place::<i32>::new("output");
//!
//!     let t = Transition::builder("process")
//!         .input(one(&p1))
//!         .output(out_place(&p2))
//!         .action(fork())
//!         .build();
//!
//!     let net = PetriNet::builder("MyWorkflow").transition(t).build();
//!
//!     generate_svg("my_workflow", &net);
//! }
//! ```
//!
//! **lib.rs:**
//! ```rust,ignore
//! /// My workflow documentation.
//! ///
//! #![doc = include_str!(concat!(env!("OUT_DIR"), "/my_workflow.svg"))]
//! ```
//!
//! The generated file is named `{name}.svg` by convention — the extension is
//! a historical "embed token", not a content-type claim. The file actually
//! contains self-contained HTML (the viewer renders the SVG at view time).

use std::env;
use std::fs;
use std::path::PathBuf;

// Re-export core types so users only need one build-dependency.
pub use libpetri_core::action::{fork, passthrough, produce, sync_action, transform};
pub use libpetri_core::arc::{inhibitor, read, reset};
pub use libpetri_core::input::{one, all, at_least, exactly};
pub use libpetri_core::instance::Instance;
pub use libpetri_core::interface::{Channel, Interface, Port, PortDirection};
pub use libpetri_core::output::{and, and_places, out_place, timeout, timeout_place, xor, xor_places};
pub use libpetri_core::petri_net::PetriNet;
pub use libpetri_core::place::{EnvironmentPlace, Place};
pub use libpetri_core::subnet_def::SubnetDef;
pub use libpetri_core::timing::{Timing, deadline, delayed, exact, immediate, window};
pub use libpetri_core::token::Token;
pub use libpetri_core::transition::Transition;

// Re-export export types under a module for advanced config.
pub use libpetri_export as export;
use libpetri_export::dot_exporter::dot_export;
use libpetri_export::mapper::DotConfig;

pub mod diagram_renderer;
pub mod subnet_dot_export;
pub mod subnet_header;

/// Generates a diagram file from a [`PetriNet`] and writes it to `OUT_DIR`.
///
/// This is the simplest entry point. It uses the default DOT export configuration
/// and automatically reads `OUT_DIR` from the environment.
///
/// The generated file is `$OUT_DIR/{name}.svg`. Embed it in rustdoc with:
/// ```rust,ignore
/// #![doc = include_str!(concat!(env!("OUT_DIR"), "/my_net.svg"))]
/// ```
///
/// Emits `cargo::rerun-if-changed=build.rs` so the file is regenerated when the
/// build script changes.
pub fn generate_svg(name: &str, net: &PetriNet) -> PathBuf {
    SvgGenerator::new().generate(name, net)
}

/// Builder for configurable diagram generation.
///
/// Use this when you need to customize the DOT export configuration or output
/// directory. For simple cases, prefer [`generate_svg`].
pub struct SvgGenerator {
    out_dir: Option<PathBuf>,
    config: DotConfig,
}

impl SvgGenerator {
    /// Creates a new generator with default settings.
    ///
    /// Output directory defaults to the `OUT_DIR` environment variable.
    pub fn new() -> Self {
        Self {
            out_dir: None,
            config: DotConfig::default(),
        }
    }

    /// Sets a custom output directory instead of `OUT_DIR`.
    pub fn out_dir(mut self, path: impl Into<PathBuf>) -> Self {
        self.out_dir = Some(path.into());
        self
    }

    /// Sets the DOT export configuration.
    pub fn config(mut self, config: DotConfig) -> Self {
        self.config = config;
        self
    }

    /// Generates the diagram file and returns its path. The host does not
    /// need any external tooling installed — the bundled viewer renders the
    /// SVG client-side.
    ///
    /// Emits `cargo::rerun-if-changed=build.rs`.
    pub fn generate(self, name: &str, net: &PetriNet) -> PathBuf {
        let out_dir = self.resolve_out_dir();
        let dot_source = dot_export(net, Some(&self.config));
        let html = diagram_renderer::render_svg(Some(net.name()), &dot_source);
        Self::write_and_announce(&out_dir, name, &html)
    }

    /// Generates an HTML wrapper for a [`SubnetDef`] and returns its path.
    /// The rendered HTML embeds the canonical `window.LibpetriViewer` bundle
    /// (CSS + JS) and the DOT source — the viewer renders the SVG and
    /// wires legend / filter chrome client-side.
    pub fn generate_subnet_def<P: 'static>(self, name: &str, def: &SubnetDef<P>) -> PathBuf {
        let out_dir = self.resolve_out_dir();
        let dot_source = subnet_dot_export::full_body(def);
        let header = subnet_header::for_subnet_def(def, false);
        let html = diagram_renderer::render_subnet_svg(def.name(), &header, &dot_source);
        Self::write_and_announce(&out_dir, name, &html)
    }

    /// Generates an HTML wrapper for an [`Instance`] and returns its path.
    /// As with [`Self::generate_subnet_def`], the SVG is rendered
    /// client-side by the bundled viewer.
    pub fn generate_instance<P: 'static>(self, name: &str, instance: &Instance<P>) -> PathBuf {
        let out_dir = self.resolve_out_dir();
        let dot_source = dot_export_instance(instance);
        let header = subnet_header::for_instance(instance);
        let title = format!("{} :: {}", instance.def_name(), instance.prefix());
        let html = diagram_renderer::render_subnet_svg(&title, &header, &dot_source);
        Self::write_and_announce(&out_dir, name, &html)
    }

    /// Generates an HTML wrapper for a composed flat [`PetriNet`] and
    /// returns its path. As with [`Self::generate_subnet_def`], the SVG is
    /// rendered client-side by the bundled viewer; cluster post-processing
    /// happens in the viewer's DOM overlay rather than via SVG mutation.
    pub fn generate_composed(self, name: &str, net: &PetriNet) -> PathBuf {
        let out_dir = self.resolve_out_dir();
        let dot_source = dot_export_composed_with_clusters(net);
        let html = diagram_renderer::render_svg(Some(net.name()), &dot_source);
        Self::write_and_announce(&out_dir, name, &html)
    }

    fn resolve_out_dir(&self) -> PathBuf {
        self.out_dir.clone().unwrap_or_else(|| {
            PathBuf::from(env::var("OUT_DIR").expect(
                "OUT_DIR not set — libpetri-docgen must be used from a build script (build.rs)",
            ))
        })
    }

    fn write_and_announce(out_dir: &std::path::Path, name: &str, content: &str) -> PathBuf {
        let svg_path = out_dir.join(format!("{name}.svg"));
        // Strip blank lines so the file stays one contiguous HTML block when
        // rustdoc embeds it via `include_str!`. CommonMark Type 6 / Type 7
        // HTML blocks terminate at the first blank line, after which any
        // 4-space-indented DOT lines become markdown indented code blocks
        // (Rust by default) and rustdoc tries to compile them. Our bundled
        // CSS and DOT source both contain blank lines naturally — they're
        // pure formatting in CSS/HTML and discarded by Graphviz, so stripping
        // them is safe.
        let compact: String = content
            .lines()
            .filter(|line| !line.trim().is_empty())
            .collect::<Vec<_>>()
            .join("\n");
        fs::write(&svg_path, &compact).expect("failed to write diagram file");
        println!("cargo::rerun-if-changed=build.rs");
        svg_path
    }
}

impl Default for SvgGenerator {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================
//  Subnet-aware helpers (mirrors Java/TS doclets per MOD-040)
// ============================================================

/// Returns the DOT source for a [`SubnetDef`] body, with the interface ports
/// restyled with the `interface-port` category and wrapped in a
/// `cluster_iface_<name>` subgraph. Mirrors Java's `SubnetDotExport.fullBody`
/// and TypeScript's `subnet-dot-export.fullBody`.
///
/// To write the rendered diagram to disk, prefer [`generate_subnet_def_svg`] or
/// the [`petrinet_doc_svg!`] macro.
pub fn dot_export_subnet_def<P: 'static>(def: &SubnetDef<P>) -> String {
    subnet_dot_export::full_body(def)
}

/// Returns the DOT source for an [`Instance`]'s renamed body. Cluster
/// `subgraph cluster_*` blocks are emitted natively by the underlying
/// [`libpetri_export::cluster_builder::partition`] step (per **MOD-040**).
pub fn dot_export_instance<P: 'static>(instance: &Instance<P>) -> String {
    dot_export(instance.renamed_body(), None)
}

/// Returns the DOT source for a composed flat [`PetriNet`], with
/// per-prefix `subgraph cluster_*` blocks for every node whose semantic
/// name carries a `/`-prefix per **MOD-040**. Cluster emission happens
/// inside [`libpetri_export::cluster_builder::partition`].
pub fn dot_export_composed_with_clusters(net: &PetriNet) -> String {
    dot_export(net, None)
}

/// Generates a diagram file from a [`SubnetDef`] and writes it to `OUT_DIR`.
///
/// Convenience entry point analogous to [`generate_svg`] but specialised for
/// subnet definitions. The rendered HTML includes the inlined CSS + JS so the
/// rustdoc viewer gets the same collapse/expand interactions as Java/TS.
pub fn generate_subnet_def_svg<P: 'static>(name: &str, def: &SubnetDef<P>) -> PathBuf {
    SvgGenerator::new().generate_subnet_def(name, def)
}

/// Generates a diagram file from an [`Instance`] and writes it to `OUT_DIR`.
pub fn generate_instance_svg<P: 'static>(name: &str, instance: &Instance<P>) -> PathBuf {
    SvgGenerator::new().generate_instance(name, instance)
}

/// Generates a diagram file from a composed flat [`PetriNet`] (with cluster
/// post-processing) and writes it to `OUT_DIR`.
pub fn generate_composed_svg(name: &str, net: &PetriNet) -> PathBuf {
    SvgGenerator::new().generate_composed(name, net)
}

/// Convenience macro: generate a diagram file and embed it in rustdoc with
/// one call.
///
/// The macro accepts a [`PetriNet`], [`SubnetDef`], or [`Instance`] expression
/// and an output filename (without `.svg`). The implementation dispatches to
/// the matching `generate_*` function via a small trait so calls remain
/// type-checked.
///
/// # Example
///
/// ```ignore
/// // build.rs
/// use libpetri_docgen::*;
///
/// fn main() {
///     let net = PetriNet::builder("flow").build();
///     petrinet_doc_svg!(&net, "flow");
/// }
/// ```
///
/// # rustdoc usage
///
/// ```rust,ignore
/// /// My documented flow.
/// #![doc = include_str!(concat!(env!("OUT_DIR"), "/flow.svg"))]
/// ```
#[macro_export]
macro_rules! petrinet_doc_svg {
    ($value:expr, $outname:literal) => {{ $crate::PetriDocSvg::generate(($value), $outname) }};
}

/// Trait dispatched-to by the [`petrinet_doc_svg!`] macro. Accepts a
/// `&PetriNet`, `&SubnetDef<P>`, or `&Instance<P>` and returns the path of
/// the written file (under `OUT_DIR`).
pub trait PetriDocSvg {
    /// Generate a diagram file for `self` under `$OUT_DIR/<outname>.svg`.
    fn generate(self, outname: &str) -> PathBuf;
}

impl PetriDocSvg for &PetriNet {
    fn generate(self, outname: &str) -> PathBuf {
        generate_svg(outname, self)
    }
}

impl<P: 'static> PetriDocSvg for &SubnetDef<P> {
    fn generate(self, outname: &str) -> PathBuf {
        generate_subnet_def_svg(outname, self)
    }
}

impl<P: 'static> PetriDocSvg for &Instance<P> {
    fn generate(self, outname: &str) -> PathBuf {
        generate_instance_svg(outname, self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn dot_export_produces_valid_dot() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let dot = dot_export(&net, None);
        assert!(dot.contains("digraph test"));
        assert!(dot.contains("p_p1"));
        assert!(dot.contains("t_t1"));
    }

    #[test]
    fn generate_to_custom_dir() {
        let p1 = Place::<i32>::new("a");
        let p2 = Place::<i32>::new("b");
        let t = Transition::builder("t")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let net = PetriNet::builder("test_gen").transition(t).build();

        let tmp = std::env::temp_dir();
        let path = SvgGenerator::new()
            .out_dir(&tmp)
            .generate("test_gen", &net);

        assert!(path.exists());
        let content = fs::read_to_string(&path).unwrap();
        // The new client-side path embeds DOT in a data-dot attribute and
        // mounts the canonical viewer; there is no inline <svg> and no
        // <pre><code class="language-text"> fallback block.
        assert!(content.contains("data-dot=\""));
        assert!(content.contains("LibpetriViewer.mount"));
        assert!(!content.contains("<pre><code class=\"language-text\">"));
        fs::remove_file(path).ok();
    }
}
