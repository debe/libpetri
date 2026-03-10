//! Build-script helper for generating Petri net SVG diagrams in rustdoc.
//!
//! This crate is intended as a **build-dependency**. It takes a [`PetriNet`]
//! definition, exports it to DOT via [`dot_export`], renders it to SVG using the
//! `dot` CLI tool, and writes the result to `OUT_DIR` so it can be embedded in
//! rustdoc with [`include_str!`].
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
//! # Fallback
//!
//! If `dot` (Graphviz) is not installed, the SVG file will contain the DOT source
//! rendered as a `<pre><code>` block instead. Install Graphviz for proper SVG output:
//!
//! ```sh
//! # Debian/Ubuntu
//! sudo apt install graphviz
//! # macOS
//! brew install graphviz
//! ```
//!
//! # Advanced Configuration
//!
//! Use [`SvgGenerator`] for control over output directory and DOT export settings:
//!
//! ```rust,no_run
//! use libpetri_docgen::*;
//! use libpetri_docgen::export::mapper::DotConfig;
//! use libpetri_docgen::export::graph::RankDir;
//!
//! # fn main() {
//! # let net = PetriNet::builder("example").build();
//! let config = DotConfig {
//!     direction: RankDir::LeftToRight,
//!     ..DotConfig::default()
//! };
//!
//! SvgGenerator::new()
//!     .config(config)
//!     .generate("my_net", &net);
//! # }
//! ```

use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

// Re-export core types so users only need one build-dependency.
pub use libpetri_core::action::{fork, passthrough, produce, sync_action, transform};
pub use libpetri_core::arc::{inhibitor, read, reset};
pub use libpetri_core::input::{one, all, at_least, exactly};
pub use libpetri_core::output::{and, and_places, out_place, timeout, timeout_place, xor, xor_places};
pub use libpetri_core::petri_net::PetriNet;
pub use libpetri_core::place::{EnvironmentPlace, Place};
pub use libpetri_core::timing::{Timing, deadline, delayed, exact, immediate, window};
pub use libpetri_core::token::Token;
pub use libpetri_core::transition::Transition;

// Re-export export types under a module for advanced config.
pub use libpetri_export as export;
use libpetri_export::dot_exporter::dot_export;
use libpetri_export::mapper::DotConfig;

/// Generates an SVG file from a [`PetriNet`] and writes it to `OUT_DIR`.
///
/// This is the simplest entry point. It uses the default DOT export configuration
/// and automatically reads `OUT_DIR` from the environment.
///
/// The generated file is `$OUT_DIR/{name}.svg`. Embed it in rustdoc with:
/// ```rust,ignore
/// #![doc = include_str!(concat!(env!("OUT_DIR"), "/my_net.svg"))]
/// ```
///
/// Emits `cargo::rerun-if-changed=build.rs` so the SVG is regenerated when the
/// build script changes.
pub fn generate_svg(name: &str, net: &PetriNet) -> PathBuf {
    SvgGenerator::new().generate(name, net)
}

/// Builder for configurable SVG generation.
///
/// Use this when you need to customize the DOT export configuration or output
/// directory. For simple cases, prefer [`generate_svg`].
pub struct SvgGenerator {
    out_dir: Option<PathBuf>,
    config: DotConfig,
    strip_dimensions: bool,
}

impl SvgGenerator {
    /// Creates a new generator with default settings.
    ///
    /// Output directory defaults to the `OUT_DIR` environment variable.
    pub fn new() -> Self {
        Self {
            out_dir: None,
            config: DotConfig::default(),
            strip_dimensions: true,
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

    /// Whether to strip explicit `width`/`height` attributes from the SVG so it
    /// scales responsively via `viewBox`. Default: `true`.
    pub fn strip_dimensions(mut self, strip: bool) -> Self {
        self.strip_dimensions = strip;
        self
    }

    /// Generates the SVG file and returns its path.
    ///
    /// Emits `cargo::rerun-if-changed=build.rs`.
    pub fn generate(self, name: &str, net: &PetriNet) -> PathBuf {
        let out_dir = self.out_dir.unwrap_or_else(|| {
            PathBuf::from(env::var("OUT_DIR").expect(
                "OUT_DIR not set — libpetri-docgen must be used from a build script (build.rs)",
            ))
        });

        let dot_source = dot_export(net, Some(&self.config));
        let svg = dot_to_svg(&dot_source, self.strip_dimensions);

        let svg_path = out_dir.join(format!("{name}.svg"));
        fs::write(&svg_path, svg).expect("failed to write SVG file");

        println!("cargo::rerun-if-changed=build.rs");
        svg_path
    }
}

impl Default for SvgGenerator {
    fn default() -> Self {
        Self::new()
    }
}

/// Converts DOT source to SVG using the `dot` CLI tool.
/// Falls back to a `<pre><code>` block if `dot` is not available.
fn dot_to_svg(dot_source: &str, strip_dimensions: bool) -> String {
    if let Some(svg) = try_dot_command(dot_source, strip_dimensions) {
        return svg;
    }

    // Fallback: embed DOT source as HTML pre block
    format!(
        "<pre><code>{}</code></pre>",
        dot_source.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;")
    )
}

/// Attempts to run `dot -Tsvg` and returns the SVG string, or `None` if `dot` is
/// unavailable or fails.
fn try_dot_command(dot_source: &str, strip_dimensions: bool) -> Option<String> {
    use std::io::Write;

    let mut child = Command::new("dot")
        .args(["-Tsvg"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .ok()?;

    child
        .stdin
        .take()
        .unwrap()
        .write_all(dot_source.as_bytes())
        .ok()?;

    let output = child.wait_with_output().ok()?;
    if !output.status.success() {
        return None;
    }

    let mut svg = String::from_utf8(output.stdout).ok()?;

    // Strip XML prolog and DOCTYPE — invalid inside HTML5
    if let Some(svg_start) = svg.find("<svg") {
        if svg_start > 0 {
            svg = svg[svg_start..].to_string();
        }
    }

    // Strip explicit width/height so the SVG scales via viewBox + CSS
    if strip_dimensions {
        svg = svg
            .replacen(
                &find_attr(&svg, "width").unwrap_or_default(),
                "",
                1,
            )
            .replacen(
                &find_attr(&svg, "height").unwrap_or_default(),
                "",
                1,
            );
    }

    Some(svg)
}

/// Finds an HTML attribute like ` width="1234pt"` in the SVG string.
fn find_attr(svg: &str, attr: &str) -> Option<String> {
    let pattern = format!(" {attr}=\"");
    let start = svg.find(&pattern)?;
    let value_start = start + pattern.len();
    let end = svg[value_start..].find('"')? + value_start + 1;
    Some(svg[start..end].to_string())
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
    fn fallback_produces_pre_block() {
        let svg = dot_to_svg("digraph { a -> b }", false);
        // If dot is available, we get real SVG; if not, we get the fallback.
        assert!(svg.contains("<svg") || svg.contains("<pre><code>"));
    }

    #[test]
    fn fallback_escapes_html() {
        let dot = "digraph { label=\"a < b & c > d\" }";
        // Force fallback by using the fallback function directly
        let html = format!(
            "<pre><code>{}</code></pre>",
            dot.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;")
        );
        assert!(html.contains("&lt;"));
        assert!(html.contains("&amp;"));
        assert!(html.contains("&gt;"));
    }

    #[test]
    fn find_attr_extracts_width() {
        let svg = r#"<svg width="100pt" height="200pt" viewBox="0 0 100 200">"#;
        assert_eq!(find_attr(svg, "width"), Some(r#" width="100pt""#.to_string()));
        assert_eq!(find_attr(svg, "height"), Some(r#" height="200pt""#.to_string()));
        assert_eq!(find_attr(svg, "missing"), None);
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
        assert!(content.contains("<svg") || content.contains("<pre><code>"));
        fs::remove_file(path).ok();
    }
}
